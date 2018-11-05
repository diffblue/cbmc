/// \file dispatch_loop_detector.h
/// \brief Find parts of a program that look like event-dispatch or server loops
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_GOTO_INSTRUMENT_DISPATCH_LOOP_DETECTOR_H
#define CPROVER_GOTO_INSTRUMENT_DISPATCH_LOOP_DETECTOR_H

#include <goto-programs/goto_functions.h>

#include <util/cmdline.h>
#include <util/cout_message.h>
#include <util/graph.h>
#include <util/options.h>

#include <forward_list>
#include <limits>
#include <list>
#include <regex>
#include <sstream>
#include <tuple>
#include <unordered_map>
#include <unordered_set>

/// \brief Detection of event-dispatch or server loops
///
/// This analysis attempts to detect so-called "dispatch loops" that lie close
/// to the program's entry point. Candidates that look like dispatch loops are
/// given a score, and this class provides an interface for accessing the source
/// location of the instruction with the highest score.
///
/// Roughly speaking, a dispatch loop is a loop that contains a conditional
/// statement. The loop repeatedly calls some function and uses the conditional
/// statement to decide what to do with the function's return value. Examples of
/// such a construct in real programs are:
///
/// - Servers, where requests are pulled from a queue, and dispatched based on
///   the type of the request;
///
/// - Graphical user interfaces, where user input events trigger some
///   computation based on what the input event is;
///
/// - Parsers and lexers, where lexemes are pulled from a queue and converted
///   into tokens;
///
/// etc. Of course, there might be many conditionals-within-a-loop in a given
/// program, and most of them will not be such dispatch loops; so we impose some
/// additional constraints:
///
/// - The dispatch loop should be close to `main()`, in particular, no more than
///   `search_depth` function calls away;
///
/// - The code transitively touched by each of the branches of the conditional
///   statement must be *reasonably* disjoint. "Transitively touched" means all
///   the code that could possibly be executed when running over a branch,
///   including all function calls, transitively. The rationale is that in a
///   dispatch loop, the conditional will be doing 'something different'
///   depending on the type of the event it is dispatching.
///
/// - The code covered by the sum of all branches of the conditional must be a
///   sizeable fraction of the entire codebase.
///
/// - The conditional must be directly nested inside the loop (this may change
///   in the future).
///
/// This class's working out can be viewed using the `--dispatch-loop-graph`
/// flag to goto-instrument, which dumps the graph that this class uses for
/// detecting the dispatch loop. The dispatch loop will be the dark node on the
/// graph.
class dispatch_loop_detectort
{
public:
  dispatch_loop_detectort(
    const goto_functionst &,
    const optionst &,
    messaget &log);

  /// \return `true` on failure, `false` otherwise
  bool detect_dispatch_loops();

protected:
  const goto_functionst &goto_functions;

  /// \brief Map from function names to lines statically reachable
  typedef std::unordered_map<irep_idt, std::set<source_locationt>, irep_id_hash>
    funs2linest;
  /// \brief Compute what lines could be executed if a function is called
  void compute_transitive_function_lines(
    funs2linest &transitive_function_lines) const;

  /// \brief Map from lines to lines statically reachable
  typedef std::map<source_locationt, std::set<source_locationt>> lines2linest;
  /// \brief Fill out a map of what lines could be touched when executing a line
  ///
  /// For function calls, this is the source location of the call plus all lines
  /// transitively touched by the function; for all other types of code, it
  /// is the singleton set containing the source location of the code itself.
  void compute_transitive_lines(
    const dispatch_loop_detectort::funs2linest &fun_map,
    dispatch_loop_detectort::lines2linest &line_map) const;

  /// \brief the set of functions that are at most `search_depth` calls away
  ///        from the entry point
  ///
  /// We will search these functions for dispatch loops.
  void find_funs_to_search(
    const std::size_t,
    const irep_idt &,
    const bool,
    std::unordered_set<irep_idt, irep_id_hash> &,
    std::unordered_map<std::string, std::unordered_set<std::string>> &);

  /// \brief Return the lines of Clang's `-ast-dump` output on the named file
  void append_ast_of_file(const std::string &, std::list<std::string> &);

  messaget &log;

  const std::size_t NO_LIMIT;

  /// \brief How many levels down the call graph from the entry point should we
  ///        search for dispatch loops?
  ///
  /// The entry point is usually __CPROVER_start, which calls main().  So if you
  /// want to search only main() for dispatch loops, this should be set to 1
  /// rather than 0.
  const std::size_t search_depth;

  /// \brief How many nodes should we allow between a loop and a decision?
  ///
  /// "Nodes" in this context consist of every node type in block_nodet::typet.
  /// If this constant is set to 1, then we will only detect dispatch loops
  /// where the decision block is directly nested within a loop; if set to 2,
  /// then the decision block may be further nested within another block, or it
  /// might be located in a function called by the loop, etc.
  const std::size_t loop_decision_distance;

  /// \brief Nodes of a simplified control-flow graph
  ///
  /// There are no individual instructions in this graph, just blocks and
  /// functions. An edge from a function node to a block indicates that the
  /// block is inside the function; conversely, an edge from a block to a
  /// function indicates that some instruction in the block calls the function.
  struct block_nodet : public graph_nodet<empty_edget>
  {
  public:
    /// \brief Generic code block types
    ///
    /// These are high-level descriptions of code blocks, since (for example) we
    /// don't typically care whether decisions in a dispatch loop are made using
    /// an if-then-else, switch, or other construct.
    enum class typet
    {
      FUNCTION,
      LOOP,
      DECISION,
      BRANCH,
      /// We need this because util/graph.h requires that node types are
      /// default-constructible, so we cannot pass a node's type into its ctor.
      DUNNO,

      /// Used when initially constructing the graph, since switch cases are
      /// unambiguously nested but if-then-elses aren't. We turn these into
      /// regular branches when calling
      /// dispatch_loop_detectort::adjust_branches(), so there should be no
      /// nodes with this type after that method is called.
      SWITCH_CASE,

      /// Nodes created during the graph's construction that we later cut off.
      /// These do not get output to DOT diagrams.
      DEAD
    };

    typet type;
    std::string label;
    std::set<source_locationt> transitive_lines;
    std::string file;
    const std::size_t NO_LINE;
    std::size_t line_begin;
    std::size_t line_end;
    const double NOT_CALCULATED;
    double disjointness;
    double score;
    bool champion;

    optionalt<goto_programt::const_targett> _first_instruction;
    optionalt<goto_programt::const_targett> _subsequent_instruction;
    optionalt<goto_programt::const_targett> _goto_instruction;

    /// \brief The first instruction executed upon entry to this loop
    const goto_programt::const_targett &first_instruction() const
    {
      INVARIANT(
        has_first_instruction(),
        "You should check whether a node has a first_instruction");
      return *_first_instruction;
    }
    bool has_first_instruction() const
    {
      INVARIANT(
        champion,
        "first_instruction is only calculated for the node considered to be "
        "the program's main dispatch loop");
      INVARIANT(
        type == typet::LOOP,
        "first_instruction is only calculated for LOOP nodes");
      return _first_instruction.has_value();
    }

    /// \brief The first instruction executed upon exit from this loop
    const goto_programt::const_targett &subsequent_instruction() const
    {
      INVARIANT(
        has_subsequent_instruction(),
        "You should check whether a node has a subsequent_instruction");
      return *_subsequent_instruction;
    }
    bool has_subsequent_instruction() const
    {
      INVARIANT(
        champion,
        "subsequent_instruction is only calculated for the node considered to "
        "be the program's main dispatch loop");
      INVARIANT(
        type == typet::LOOP,
        "subsequent_instruction is only calculated for LOOP nodes");
      return _subsequent_instruction.has_value();
    }

    /// \brief The `GOTO` instruction associated with this branch of a decision
    const goto_programt::const_targett &goto_instruction() const
    {
      INVARIANT(
        has_goto_instruction(),
        "You should check whether a node has a goto_instruction");
      return *_goto_instruction;
    }
    bool has_goto_instruction() const
    {
      INVARIANT(
        champion,
        "goto_instruction is only calculated for the node considered to "
        "be a branch program's main dispatch loop");
      INVARIANT(
        type == typet::BRANCH,
        "goto_instruction is only calculated for BRANCH nodes");
      return _goto_instruction.has_value();
    }

    /// \brief The first instruction executed upon entry to this loop
    goto_programt::const_targett &first_instruction()
    {
      return const_cast<goto_programt::const_targett &>(
        static_cast<const block_nodet &>(*this).first_instruction());
    }

    /// \brief The first instruction executed upon exit from this loop
    goto_programt::const_targett &subsequent_instruction()
    {
      return const_cast<goto_programt::const_targett &>(
        static_cast<const block_nodet &>(*this).subsequent_instruction());
    }

    /// \brief The `GOTO` instruction associated with this branch of a decision
    goto_programt::const_targett &goto_instruction()
    {
      return const_cast<goto_programt::const_targett &>(
        static_cast<const block_nodet &>(*this).goto_instruction());
    }

    block_nodet();

    /// Fake 'constructor,' since util/graph.h needs nodes to be default-
    /// constructible
    void init(
      const typet,
      const std::string &,
      const std::string &,
      const std::size_t,
      const std::size_t);

    inline bool is_function(const std::string &fun_name) const;
    bool operator==(const block_nodet &other) const;
    virtual std::string dot_attributes(const node_indext &idx) const override;

  protected:
    std::string shape() const;
    std::string text() const;
    std::string colour() const;
  };

public:
  grapht<block_nodet> graph;
  const std::string key;

protected:
  bool build_graph(
    const std::map<std::string, std::list<std::string>> &,
    const std::unordered_map<std::string, std::unordered_set<std::string>> &,
    std::map<std::string, block_nodet::node_indext> &);

  void add_functions_to_graph(
    const std::string &,
    const std::list<std::string> &,
    const std::map<std::string, block_nodet::node_indext> &,
    std::unordered_set<std::string> &);

  const std::size_t NO_ELSE;

  void add_nodes_to_graph(
    const std::string &,
    const block_nodet::node_indext &,
    std::list<std::string>::const_iterator,
    std::list<std::string>::const_iterator,
    const std::size_t,
    std::size_t &,
    std::size_t);

  void add_single_node(
    const std::smatch &,
    const std::string &,
    const block_nodet::node_indext &,
    const block_nodet::typet,
    const std::size_t begin_line,
    const std::size_t end_line,
    block_nodet::node_indext &);

  /// \brief Convert the cases of an if-then-else into cases
  ///
  /// Due to the shape of Clang's AST, the add_nodes_to_graph() method can't
  /// distinguish between nested and sibling if-elses. This method changes all
  /// sibling branches into block_nodet::typet::BRANCH and makes them into
  /// children of a new block_nodet::typet::DECISION node.
  void adjust_branches(
    const block_nodet::node_indext &,
    const block_nodet::node_indext &,
    const std::size_t,
    const std::size_t,
    std::set<block_nodet::node_indext> &);

  void single_node_branch_adjust(
    const block_nodet::node_indext &,
    const block_nodet::node_indext &);

  /// \brief Get a map of functions that call each other
  ///
  /// There will be an entry {F -> {n -> {G}}} in this map if there is a call to
  /// function G() in line n of function F(), and both F() and G() are functions
  /// that are at most `search_depth` calls away from the entry point.
  void get_call_map(
    const std::unordered_set<irep_idt, irep_id_hash> &,
    std::unordered_map<
      std::string,
      std::unordered_map<std::size_t, std::string>> &);

  /// \brief Add edges from internal nodes to the function nodes that they call
  void add_call_edges(
    const std::unordered_map<std::size_t, std::string> &,
    const std::map<std::string, block_nodet::node_indext> &fun2idx,
    const block_nodet::node_indext &,
    std::set<block_nodet::node_indext> &);

  void get_indicies_of_all_nodes(
    const std::map<std::string, block_nodet::node_indext> &,
    std::set<block_nodet::node_indext> &);

  void add_transitive_lines_to_branches(
    const lines2linest &,
    const std::set<block_nodet::node_indext> &);

  void compute_disjointness(const std::set<block_nodet::node_indext> &);

  void make_dispatch_branches_into_champions(const block_nodet::node_indext &);

  /// \return `true` on failure, `false` otherwise
  bool find_dispatch_loop(const std::set<block_nodet::node_indext> &);

  /// \brief What is the graph distance between this node and a champion node?
  ///
  /// This function should initially be called with the index of a loop node,
  /// which by definition will not be a champion node when this function is
  /// called. Thus a return value of zero means "there are no champion
  /// descendants", and a return value of 1 means "there is a champion that is a
  /// direct successor of this node".
  ///
  /// \return 0 if there does not exist a champion node within the specified
  ///         bound. A positive integer indicating how many edges must be
  ///         followed to reach a champion node otherwise.
  int distance_to_champion_descendants(
    const grapht<block_nodet>::node_indext &,
    const int,
    std::unordered_set<grapht<block_nodet>::node_indext> &);

  /// \brief Look for the first instruction that comes after the loop
  ///
  /// This is called the "subsequent instruction". The set `loop_set` now
  /// contains all the program locations that are in the dispatch loop. One of
  /// those locations will be the loop guard (which might not be the same as the
  /// first instruction in the loop); the loop guard will lead us to the
  /// "subsequent instruction".
  ///
  /// We consider the "loop guard" to be a conditional goto, which must be
  /// either the first or the last instruction in the loop. If it is the first
  /// instruction in the loop, then its target will be the subsequent
  /// instruction; if the loop guard is the last instruction in the loop, then
  /// its next instruction will be the subsequent instruction. In both cases,
  /// check that the subsequent instruction is not itself inside the loop.
  void find_subsequent_instruction(
    const block_nodet::node_indext &,
    const std::set<goto_programt::const_targett> &);

  /// \brief How deeply nested is the node in a line of a Clang AST?
  std::size_t nesting_depth(const std::smatch &match) const
  {
    return match[1].length();
  }

  ///@{\name Clang AST regex matchers
  ///
  /// Members of type std::size_t are capture groups for the regex whose name
  /// they share.

  /// \brief This should match any line of an AST.
  const std::regex re_catch_all;

  const std::regex re_function_decl;
  const std::size_t re_function_decl_LINE_BEGIN;
  const std::size_t re_function_decl_LINE_END;
  const std::size_t re_function_decl_FUNCTION_NAME;

  const std::regex re_if_stmt;
  const std::size_t re_if_stmt_TYPE;

  const std::regex re_switch_stmt;
  const std::regex re_case_stmt;
  const std::regex re_default_stmt;
  const std::regex re_while_stmt;
  const std::regex re_for_stmt;
  const std::regex re_do_stmt;

  /// \brief Matches the last child of an AST subtree
  const std::regex re_last_child;
  const std::size_t re_last_child_PAYLOAD;

  /// \brief The last line of an AST whose node has both a begin and an end line
  const std::regex re_last_child_both_lines;
  /// \brief The last line of an AST, where the node has only an end line
  const std::regex re_last_child_start_only;
  const std::size_t re_last_child_both_lines_FILE;
  const std::size_t re_last_child_both_lines_BEGIN;
  const std::size_t re_last_child_both_lines_END;

  /// \brief What graph node should be made, and how, when a regex is matched?
  ///
  /// Map from regexes to what type of graph node should be made, plus the
  /// capture groups of the regex that refer to the line number range of the AST
  /// node.
  const std::forward_list<std::pair<
    std::regex,
    std::tuple<block_nodet::typet, std::size_t, std::size_t>>>
    re_jump_table;

  ///@}

  /// Map from filenames to their contents
  std::map<std::string, std::vector<std::string>> source_code;
  std::string get_line_of_file(const std::string &, const std::size_t) const;
  void read_source_code(
    const std::unordered_map<std::string, std::unordered_set<std::string>>
      &files);

  /// \brief Make lines of code from a file prettier for display in a graph
  const std::forward_list<std::pair<std::regex, std::string>> line_replacements;

  const source_locationt &sloc_of(const goto_programt::const_targett &ins) const
  {
    return ins->code.source_location().is_not_nil()
             ? ins->code.source_location()
             : ins->source_location;
  }

  source_locationt &sloc_of(const goto_programt::const_targett &ins)
  {
    return const_cast<source_locationt &>(
      static_cast<const dispatch_loop_detectort &>(*this).sloc_of(ins));
  }

  const source_locationt &sloc_of(const goto_programt::instructiont &ins) const
  {
    return ins.code.source_location().is_not_nil() ? ins.code.source_location()
                                                   : ins.source_location;
  }

  source_locationt &sloc_of(const goto_programt::instructiont &ins)
  {
    return const_cast<source_locationt &>(
      static_cast<const dispatch_loop_detectort &>(*this).sloc_of(ins));
  }

public:
  struct dispatch_loopt
  {
  public:
    dispatch_loopt(const dispatch_loop_detectort &);
    const goto_functionst &goto_functions;

  protected:
    const grapht<block_nodet> &graph;
    messaget &log;
    void get_all_nodes(std::forward_list<block_nodet::node_indext> &) const;

    bool lines_match(
      const block_nodet::node_indext &,
      const goto_programt::const_targett &) const;

    void try_assigning_first_and_subsequent(
      const block_nodet::node_indext &,
      optionalt<goto_programt::const_targett> &,
      optionalt<goto_programt::const_targett> &) const;

    void try_assigning_case_beginning(
      const block_nodet::node_indext &,
      const goto_programt::const_targett &,
      std::set<goto_programt::const_targett> &) const;

    /// We pack all of the "members" of this struct into a single tuple. This
    /// allows us to construct all of them with a single function call, for
    /// efficiency reasons, since each member needs a loop-over-all-instructions
    /// within a loop-over-all-graph-nodes. Actually accessing the members is
    /// done with the public accessor functions below.
    typedef const std::tuple<
      goto_programt::const_targett,
      std::set<goto_programt::const_targett>,
      goto_programt::const_targett>
      memberst;
    memberst members;
    memberst build_members() const;

  public:
    /// This might not be the "loop head,"---in particular, it won't be for a
    /// `do-while` loop. The "first instruction" is the lexicographically first
    /// goto-instruction that will be executed when the loop is first
    /// encountered.
    const goto_programt::const_targett first_instruction() const
    {
      return std::get<0>(members);
    }
    /// These don't need to be 'in' the loop; they might be in a function called
    /// from the loop, for example.
    const std::set<goto_programt::const_targett> &cases() const
    {
      return std::get<1>(members);
    }
    /// \brief The first instruction after the end of the dispatch loop
    ///
    /// This will be the first instruction that gets executed after the loop
    /// guard evaluates to `false`. We don't deal with the case of unstructured
    /// programming, e.g. the C program contains a `goto` statement that jumps
    /// out of the middle of the loop and lands somewhere unrelated.
    const goto_programt::const_targett &subsequent_instruction() const
    {
      return std::get<2>(members);
    }
  };

  static void set_front_end_options(const cmdlinet &, optionst &);
};

#define OPT_DISPATCH_LOOP_DETECTION                                            \
  "(dispatch-loop-graph)(dispatch-loop-location)"                              \
  "(dispatch-function-search-depth):(dispatch-loop-decision-distance):"

#define HELP_DISPATCH_LOOP_DETECTION                                           \
  " --dispatch-loop-graph        print a DOT graph showing the dispatch "      \
  "loop\n"                                                                     \
  " --dispatch-loop-location     print source location of the dispatch loop\n"

#endif // CPROVER_GOTO_INSTRUMENT_DISPATCH_LOOP_DETECTOR_H
