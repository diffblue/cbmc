/*******************************************************************\

Module: Dispatch Loop Detector

Author: Kareem Khazem <karkhaz@karkhaz.com>

\*******************************************************************/

#include "dispatch_loop_detector.h"

#include <analyses/natural_loops.h>

#include <util/file_util.h>
#include <util/optional.h>
#include <util/run.h>
#include <util/string2int.h>
#include <util/tempfile.h>

#include <algorithm>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iterator>
#include <vector>

// String literals, so that we can build up regexes by preprocessor
// concatenation rather than wasting time at runtime.
#define RE_HEX R"( 0x[abcdef0-9]+ )"
#define RE_FLAGS , std::regex::ECMAScript | std::regex::optimize

// The beginning of a line of Clang's AST.
//
// Clang emits an AST formatted as a tree, with the tree's structure formatted
// using a string of the characters -, `, |, and whitespace at the beginning of
// each line. We invariably want to skip past all of that. However, the width of
// those characters tells us about the nesting depth of whatever comes
// afterwards, so we need to measure the length of the matched string even if we
// don't care about its exact shape. Thus, in all later regexes in this class,
// the tree-structure-string will be match group 1 (group 0 is the whole match).
#define RE_INIT R"(([\s\|\-`]+))"

dispatch_loop_detectort::dispatch_loop_detectort(
  const goto_functionst &gf,
  const optionst &options,
  messaget &log)
  : goto_functions(gf),
    log(log),
    NO_LIMIT(std::numeric_limits<std::size_t>::max()),
    search_depth(
      options.is_set("dispatch-function-search-depth")
        ? options.get_signed_int_option("dispatch-function-search-depth") == 0
            ? NO_LIMIT
            : options.get_signed_int_option("dispatch-function-search-depth")
        : 2),
    loop_decision_distance(
      options.is_set("dispatch-loop-decision-distance")
        ? options.get_signed_int_option("dispatch-loop-decision-distance")
        : 2),
    key(
      R"(a -> b -> c -> d -> e [color="#ffffff"];)"
      R"(a [shape="none", label="Key:"];)"
      R"(b [shape="house", label="Function", style="filled", color="#f8bbd0"];)"
      R"+(c [shape="egg", label="Loop (for/while/do-while)", style="filled",)+"
      R"(   color="#ffccbc"];)"
      R"+(d [shape="diamond", label="Decision (if/switch)", style="filled",)+"
      R"(   color="#bbdefb"];)"
      R"(e [shape="box", label="Case", style="filled", color="#d7ccc8"];)"),
    NO_ELSE(std::numeric_limits<std::size_t>::max()),
    re_catch_all(RE_INIT R"(.+?)" RE_FLAGS),
    // To understand what these regexes are matching, write a small C program
    // with if-elses, while loops etc. and run `clang -Xclang -ast-dump foo.c`.
    re_function_decl(RE_INIT
                     R"(FunctionDecl)" RE_HEX R"((?:prev)" RE_HEX R"()?)"
                     R"(<.+?:(\d+))"
                     R"(:\d+, .+?:(\d+):\d+> .+?:\d+:\d+ )"
                     R"((?:implicit )?(?:invalid )?(?:referenced )?(?:used )?)"
                     R"((\w+).+)" RE_FLAGS),
    re_function_decl_LINE_BEGIN(2),
    re_function_decl_LINE_END(3),
    re_function_decl_FUNCTION_NAME(4),
    re_if_stmt(RE_INIT R"((IfStmt))" RE_HEX R"(<.+?:(\d+):\d+, )"
                       R"(.+?:(\d+):\d+>)" RE_FLAGS),
    re_if_stmt_TYPE(2),
    re_switch_stmt(RE_INIT R"(SwitchStmt)" RE_HEX
                           R"(<.+?:(\d+):\d+, .+?:(\d+):\d+>)" RE_FLAGS),
    re_case_stmt(RE_INIT R"(CaseStmt)" RE_HEX
                         R"(<.+?:(\d+):\d+, .+?:(\d+):\d+>)" RE_FLAGS),
    re_default_stmt(RE_INIT R"(DefaultStmt)" RE_HEX
                            R"(<.+?:(\d+):\d+, .+?:(\d+):\d+>)" RE_FLAGS),
    re_while_stmt(RE_INIT R"(WhileStmt)" RE_HEX
                          R"(<.+?:(\d+):\d+, .+?:(\d+):\d+>)" RE_FLAGS),
    re_for_stmt(RE_INIT R"(ForStmt)" RE_HEX
                        R"(<.+?:(\d+):\d+, .+?:(\d+):\d+>)" RE_FLAGS),
    re_do_stmt(RE_INIT R"(DoStmt)" RE_HEX
                       R"(<.+?:(\d+):\d+, .+?:(\d+):\d+>)" RE_FLAGS),
    re_last_child(RE_INIT R"(`\-(.+))" RE_FLAGS),
    re_last_child_PAYLOAD(2),
    re_last_child_both_lines(RE_INIT
                             R"(.+<(.+?):(\d+):\d+, .+?:(\d+):\d+>)" RE_FLAGS),
    re_last_child_start_only(RE_INIT R"(.+<(.+?):(\d+):\d+, .+)" RE_FLAGS),
    re_last_child_both_lines_FILE(2),
    re_last_child_both_lines_BEGIN(3),
    re_last_child_both_lines_END(4),
    re_jump_table({
      {re_if_stmt, {block_nodet::typet::DECISION, 3, 4}},
      {re_while_stmt, {block_nodet::typet::LOOP, 2, 3}},
      {re_for_stmt, {block_nodet::typet::LOOP, 2, 3}},
      {re_switch_stmt, {block_nodet::typet::DECISION, 2, 3}},
      {re_case_stmt, {block_nodet::typet::SWITCH_CASE, 2, 3}},
      {re_default_stmt, {block_nodet::typet::SWITCH_CASE, 2, 3}},
      {re_do_stmt, {block_nodet::typet::LOOP, 2, 3}},
    }),
    line_replacements({
      {std::regex(R"(^\s+)" RE_FLAGS), ""},
      {std::regex(R"(")" RE_FLAGS), R"(\")"},
      {std::regex(R"(/\*.+?\*/)" RE_FLAGS), ""},
      {std::regex(R"(//.+$)" RE_FLAGS), ""},
      {std::regex(R"(\s+$)" RE_FLAGS), ""},
    })
{
  if(loop_decision_distance == 0)
    log.warning() << "No dispatch loops will be detected with "
                  << "loop_decision_distance set to 0. Set it to 1 to search "
                  << "only for loops whose decision is directly nested inside "
                  << "the loop" << log.eom;
}

bool dispatch_loop_detectort::detect_dispatch_loops()
{
  funs2linest funs2lines;
  compute_transitive_function_lines(funs2lines);

  lines2linest lines2lines;
  compute_transitive_lines(funs2lines, lines2lines);

  std::unordered_set<irep_idt, irep_id_hash> close_to_entry;
  std::unordered_map<std::string, std::unordered_set<std::string>> to_search;
  find_funs_to_search(
    search_depth,
    goto_functions.entry_point(),
    true,
    close_to_entry,
    to_search);
  log.debug() << "Searching for dispatch loops in the functions [ ";
  for(const auto &fun : close_to_entry)
    log.debug() << fun << " ";
  log.debug() << "]" << log.eom;

  std::map<std::string, std::list<std::string>> asts;
  for(const auto &pair : to_search)
  {
    std::list<std::string> &ast = asts[pair.first];
    append_ast_of_file(pair.first, ast);
  }

  read_source_code(to_search);
  std::map<std::string, block_nodet::node_indext> fun2idx;
  bool fail = build_graph(asts, to_search, fun2idx);
  source_code.clear();
  if(fail)
    return true;

  std::unordered_map<std::string, std::unordered_map<std::size_t, std::string>>
    call_map;
  get_call_map(close_to_entry, call_map);
  for(const auto &pair : call_map)
  {
    std::set<block_nodet::node_indext> already_seen;
    add_call_edges(pair.second, fun2idx, fun2idx.at(pair.first), already_seen);
  }

  std::set<block_nodet::node_indext> all_nodes;
  get_indicies_of_all_nodes(fun2idx, all_nodes);

  add_transitive_lines_to_branches(lines2lines, all_nodes);

  compute_disjointness(all_nodes);

  return find_dispatch_loop(all_nodes);
}

bool dispatch_loop_detectort::build_graph(
  const std::map<std::string, std::list<std::string>> &asts,
  const std::unordered_map<std::string, std::unordered_set<std::string>>
    &file2funs,
  std::map<std::string, block_nodet::node_indext> &fun2idx)
{
  for(const auto &pair : file2funs)
  {
    for(const auto &fun_name : pair.second)
    {
      block_nodet::node_indext idx = graph.add_node();
      fun2idx.insert(std::make_pair(std::string(fun_name.c_str()), idx));
    }
  }

  bool fail = false;
  for(const auto &pair : file2funs)
  {
    const auto file_ast = asts.find(pair.first);
    INVARIANT(
      file_ast != asts.end(),
      "The ASTs map should contain an AST for each file that we want to find "
      "functions in.");

    log.debug() << "Parsing AST of file '" << file_ast->first << "'" << log.eom;

    std::unordered_set<std::string> funs_of_file(pair.second);
    add_functions_to_graph(
      file_ast->first, file_ast->second, fun2idx, funs_of_file);

    if(!funs_of_file.empty())
    {
      fail = true;
      log.error() << "Could not find the following functions in the file '"
                  << file_ast->first << "': [ ";
      for(const auto &fun : funs_of_file)
        log.error() << fun << " ";
      log.error() << "]" << log.eom;
    }
  }

  return fail;
}

void dispatch_loop_detectort::add_functions_to_graph(
  const std::string &file,
  const std::list<std::string> &ast,
  const std::map<std::string, block_nodet::node_indext> &fun2idx,
  std::unordered_set<std::string> &functions)
{
  std::smatch m;

  std::size_t skip_counter = 0;
  for(auto line = ast.begin(); line != ast.end(); ++line)
  {
    // If we've just parsed a function, fast-forward through the lines of that
    // function.
    if(skip_counter > 0)
    {
      --skip_counter;
      continue;
    }

    if(std::regex_match(*line, m, re_function_decl))
    {
      log.debug() << "Found function '" << m[re_function_decl_FUNCTION_NAME]
                  << "' at line " << m[re_function_decl_LINE_BEGIN] << log.eom;
      const auto &found = functions.find(m[re_function_decl_FUNCTION_NAME]);
      if(found != functions.end())
      {
        functions.erase(found);

        const std::string &fun_name = m[re_function_decl_FUNCTION_NAME];
        const block_nodet::node_indext &fun_idx = fun2idx.at(fun_name);
        block_nodet &fun_node = graph[fun_idx];
        fun_node.init(
          block_nodet::typet::FUNCTION,
          fun_name.c_str(),
          file,
          std::stol(m[re_function_decl_LINE_BEGIN]),
          std::stol(m[re_function_decl_LINE_END]));

        add_nodes_to_graph(
          file,
          fun_idx,
          std::next(line),
          ast.end(),
          nesting_depth(m),
          skip_counter,
          NO_ELSE);

        // We've just added an entire function. Adjust the cases of the ifs.
        std::set<block_nodet::node_indext> already_seen;
        adjust_branches(
          fun_idx,
          fun_idx,
          graph[fun_idx].line_begin,
          graph[fun_idx].line_end,
          already_seen);
      }
    }
  }
}

void dispatch_loop_detectort::add_nodes_to_graph(
  const std::string &file_name,
  const block_nodet::node_indext &parent_idx,
  std::list<std::string>::const_iterator ast_begin,
  std::list<std::string>::const_iterator ast_end,
  const std::size_t parent_nesting_depth,
  std::size_t &skip_counter,
  std::size_t else_nesting_depth)
{
  std::smatch m;
  std::size_t local_skip_counter = 0;
  for(auto line = ast_begin; line != ast_end; ++line)
  {
    // The recursive call to add_nodes_to_graph may have advanced
    // local_skip_counter; we don't want to process those lines again. So skip
    // them; at the same time, indicate to our parent caller that _they_ should
    // also not process those lines again by advancing skip_counter.
    if(local_skip_counter > 0)
    {
      --local_skip_counter;
      ++skip_counter;
      continue;
    }

    std::size_t current_nesting_depth;
    block_nodet::node_indext new_parent = parent_idx;

    if(std::regex_match(*line, m, re_catch_all))
    {
      current_nesting_depth = nesting_depth(m);
      if(current_nesting_depth <= parent_nesting_depth)
        return;
    }

    block_nodet::typet block_type;
    std::size_t line_begin_group, line_end_group;
    bool recognised_line = false;
    bool recognised_if = false;
    bool recognised_else = false;

    for(const auto &pair : re_jump_table)
      if(std::regex_match(*line, m, pair.first))
      {
        block_type = std::get<0>(pair.second);
        line_begin_group = std::get<1>(pair.second);
        line_end_group = std::get<2>(pair.second);
        recognised_line = true;
        if(m[re_if_stmt_TYPE] == "IfStmt")
          recognised_if = true;
        break;
      }

    // Perhaps we didn't recognise the line because it's an else branch
    if(
      !recognised_line && else_nesting_depth == current_nesting_depth &&
      std::regex_match(*line, m, re_last_child))
    {
      const std::string &payload = m[re_last_child_PAYLOAD];

      if(
        std::regex_match(*line, m, re_last_child_both_lines) &&
        (m[re_last_child_both_lines_FILE] == "line" ||
         m[re_last_child_both_lines_FILE] == file_name))
      {
        log.debug() << "Found else: " << payload << log.eom;
        recognised_line = true;
        recognised_if = true;
        recognised_else = true;
        block_type = block_nodet::typet::DECISION;
        line_begin_group = re_last_child_both_lines_BEGIN;
        line_end_group = re_last_child_both_lines_END;
        else_nesting_depth = NO_ELSE;
      }
      else if(
        std::regex_match(*line, m, re_last_child_start_only) &&
        (m[re_last_child_both_lines_FILE] == "line" ||
         m[re_last_child_both_lines_FILE] == file_name))
      {
        log.debug() << "Found else: " << payload << log.eom;
        recognised_line = true;
        recognised_if = true;
        recognised_else = true;
        block_type = block_nodet::typet::DECISION;
        line_begin_group = re_last_child_both_lines_BEGIN;
        line_end_group = re_last_child_both_lines_BEGIN;
        else_nesting_depth = NO_ELSE;
      }
    }

    if(recognised_line)
    {
      add_single_node(
        m,
        file_name,
        parent_idx,
        block_type,
        line_begin_group,
        line_end_group,
        new_parent);

      if(recognised_if)
      {
        // If is a special case, because the 'else' branch doesn't have its own
        // node type; it might be a CompoundStmt, NULL, or something else.
        // However, it will always be the last child of the if sub-tree, and
        // therefore its tree marker will end with the string "`-", indented 2
        // more spaces than the current nesting depth. So tell the recursive
        // call to look for that.
        if(!recognised_else)
        {
          else_nesting_depth = current_nesting_depth + 2;
          log.debug() << "At line " << graph[new_parent].line_begin
                      << ", setting else nesting depth to "
                      << else_nesting_depth << log.eom;
        }

        // Deal with clang printing else-ifs as children
        if(
          graph[parent_idx].type == block_nodet::typet::DECISION &&
          graph[parent_idx].line_end == graph[new_parent].line_end)
        {
          log.debug() << "Adjusting nesting depth of if statement at line "
                      << graph[new_parent].line_begin << " to "
                      << parent_nesting_depth << " with parent at line "
                      << graph[parent_idx].line_begin << log.eom;
          current_nesting_depth = parent_nesting_depth;
          new_parent = parent_idx;
        }
      }
      add_nodes_to_graph(
        file_name,
        new_parent,
        std::next(line),
        ast_end,
        current_nesting_depth,
        local_skip_counter,
        else_nesting_depth);
    }
    ++skip_counter;
  }
}

void dispatch_loop_detectort::add_single_node(
  const std::smatch &m,
  const std::string &file_name,
  const block_nodet::node_indext &parent_index,
  const block_nodet::typet block_type,
  const std::size_t begin_line_match_group,
  const std::size_t end_line_match_group,
  block_nodet::node_indext &node_index)
{
  node_index = graph.add_node();
  graph[node_index].init(
    block_type,
    get_line_of_file(file_name, std::stol(m[begin_line_match_group])),
    file_name,
    std::stol(m[begin_line_match_group]),
    std::stol(m[end_line_match_group]));
  graph.add_edge(parent_index, node_index);
}

void dispatch_loop_detectort::adjust_branches(
  const block_nodet::node_indext &parent,
  const block_nodet::node_indext &current,
  const std::size_t fun_begin,
  const std::size_t fun_end,
  std::set<block_nodet::node_indext> &seen)
{
  if(seen.find(current) != seen.end())
    return;
  seen.insert(current);

  if(
    (graph[current].line_begin < fun_begin ||
     graph[current].line_end > fun_end) &&
    graph.get_successors(current).empty())
  {
    graph.remove_edge(parent, current);
    graph[current].type = block_nodet::typet::DEAD;
    return;
  }

  if(
    graph[current].type == block_nodet::typet::DECISION ||
    graph[current].type == block_nodet::typet::BRANCH)
  {
    single_node_branch_adjust(parent, current);
  }
  else if(graph[current].type == block_nodet::typet::SWITCH_CASE)
    graph[current].type = block_nodet::typet::BRANCH;

  for(const auto &succ : graph.get_successors(current))
    adjust_branches(current, succ, fun_begin, fun_end, seen);
}

void dispatch_loop_detectort::single_node_branch_adjust(
  const block_nodet::node_indext &parent,
  const block_nodet::node_indext &current)
{
  log.debug() << "single_node_branch adjust for " << current << ", " << parent
              << log.eom;

  std::forward_list<std::pair<std::size_t, std::size_t>> line_ranges;
  for(const auto &child : graph.get_successors(current))
  {
    if(graph[child].type != block_nodet::typet::DECISION)
      return;
    line_ranges.push_front({graph[child].line_begin, graph[child].line_end});
  }

  log.debug() << "Found something with all-DECISION children" << log.eom;

  if(line_ranges.empty())
  {
    graph[current].type = block_nodet::typet::BRANCH;
    log.debug() << "Turning current into BRANCH and returning" << log.eom;
    return;
  }

  line_ranges.sort();
  std::size_t last_begin = line_ranges.front().first - 1;
  std::size_t end_of_then = graph[current].NO_LINE;
  for(const auto &pair : line_ranges)
  {
    log.debug() << "Range " << pair.first << ", " << pair.second << log.eom;
    int gap;
    if(
      pair.first == graph[current].NO_LINE ||
      pair.second == graph[current].NO_LINE ||
      !(gap = pair.first - last_begin) || gap < 0)
    {
      log.debug() << "Returning because the gap between branches is too large. "
                     "Gap is "
                  << gap << " last_begin is " << last_begin << "end_of_then is "
                  << end_of_then << "line range first is " << pair.first
                  << log.eom;
      return;
    }
    last_begin = pair.first;
    if(end_of_then == graph[current].NO_LINE)
      end_of_then = pair.first - 1;
  }

  log.debug() << "Reached for " << parent << " -> " << current << log.eom;

  // If we got here, current should actually be a sibling of all its
  // children, and both current and its children should be BRANCHes.
  block_nodet::node_indext new_decision = graph.add_node();
  graph[new_decision].init(
    block_nodet::typet::DECISION,
    graph[current].label,
    graph[current].file,
    graph[current].line_begin,
    graph[current].line_end);
  graph.remove_edge(parent, current);
  graph.add_edge(parent, new_decision);
  graph.add_edge(new_decision, current);
  for(const auto &child : graph.get_successors(current))
    graph.add_edge(new_decision, child);
  for(const auto &child : graph.get_successors(current))
  {
    graph[child].type = block_nodet::typet::BRANCH;
    graph.remove_edge(current, child);
  }

  graph[current].line_end = end_of_then;
  graph[current].type = block_nodet::typet::BRANCH;

  // At this point, the line_end of all of the branches will be the same: it
  // will be the line number of the end of the entire block. Change them to be
  // the line number of the next branch.
  line_ranges.reverse();
  last_begin = line_ranges.front().second + 1;
  for(const auto &pair : line_ranges)
    for(const auto &child : graph.get_successors(new_decision))
    {
      if(graph[child].line_begin != pair.first)
        continue;
      graph[child].line_end = last_begin - 1;
      last_begin = graph[child].line_begin;
      break;
    }
}

void dispatch_loop_detectort::append_ast_of_file(
  const std::string &file,
  std::list<std::string> &ast)
{
  temporary_filet clang_outfile("cprover_clang-parse-tree", "out");
  temporary_filet clang_errfile("cprover_clang-parse-tree", "err");
  std::vector<std::string> argv = {
    "clang", "-Xclang", "-ast-dump", "-Xclang", "-fno-color-diagnostics", file};

  // Ignore the return code. Clang will often return non-zero when parsing an
  // individual file (because it doesn't know where included headers live, etc)
  // but this doesn't preclude it from producing a valid AST.
  run(argv[0], argv, "", clang_outfile(), clang_errfile());

  std::ifstream inf(clang_outfile());
  std::string tmp;
  while(std::getline(inf, tmp))
    ast.push_back(tmp);
  inf.close();
}

void dispatch_loop_detectort::compute_transitive_lines(
  const dispatch_loop_detectort::funs2linest &fun_map,
  dispatch_loop_detectort::lines2linest &line_map) const
{
  forall_goto_functions(f_it, goto_functions)
  {
    forall_goto_program_instructions(ins, f_it->second.body)
    {
      const source_locationt &loc = ins->source_location.is_nil()
                                      ? ins->code.source_location()
                                      : ins->source_location;
      if(loc.is_nil())
        continue;

      std::set<source_locationt> &loc_set = line_map[loc];

      if(ins->is_function_call())
      {
        const code_function_callt &call = to_code_function_call(ins->code);
        if(call.function().is_nil())
          continue;
        const irep_idt &call_name = call.function().get("identifier");

        if(std::strlen(call_name.c_str()) == 0)
          continue;

        const auto found = fun_map.find(call_name);
        INVARIANT(
          found != fun_map.end(),
          "Could not find the call to " + std::string(call_name.c_str()) +
            " in the function map, called from " + f_it->first.c_str());

        loc_set.insert(
          fun_map.at(call_name).begin(), fun_map.at(call_name).end());
      }

      loc_set.insert(loc);
    }
  }
}

void dispatch_loop_detectort::compute_transitive_function_lines(
  dispatch_loop_detectort::funs2linest &trans_lines) const
{
  std::list<irep_idt> worklist;

  forall_goto_functions(f_it, goto_functions)
  {
    if(f_it->first.empty())
      continue;

    worklist.push_back(f_it->first);

    std::set<source_locationt> &line_set = trans_lines[f_it->first];
    forall_goto_program_instructions(it, f_it->second.body)
    {
      if(it->source_location.is_not_nil())
        line_set.insert(it->source_location);
      else if(it->code.source_location().is_not_nil())
        line_set.insert(it->code.source_location());
    }
  }

  while(!worklist.empty())
  {
    const auto explore_it = goto_functions.function_map.find(worklist.front());

    bool updated = false;
    forall_goto_program_instructions(ins, explore_it->second.body)
    {
      if(!ins->is_function_call())
        continue;
      const code_function_callt &call = to_code_function_call(ins->code);
      if(call.function().is_nil())
        continue;
      const irep_idt &call_name = call.function().get("identifier");
      if(std::strlen(call_name.c_str()) == 0)
        continue;

      // Check for this here rather than when we pop the worklist, so that we
      // know both the name of the call and also where it's called from (i.e.
      // worklist.front()).
      INVARIANT(
        goto_functions.function_map.find(call_name) !=
          goto_functions.function_map.end(),
        "Could not find function '" + std::string(call_name.c_str()) +
          "', called from function '" + std::string(worklist.front().c_str()) +
          "', in function map");

      for(const auto &child : trans_lines[call_name])
        updated |= trans_lines[worklist.front()].insert(child).second;
    }

    if(updated)
      worklist.push_back(worklist.front());
    worklist.pop_front();
  }
}

void dispatch_loop_detectort::find_funs_to_search(
  const std::size_t level,
  const irep_idt &fun,
  const bool is_entry_point,
  std::unordered_set<irep_idt, irep_id_hash> &fast_lookup,
  std::unordered_map<std::string, std::unordered_set<std::string>> &accumulator)
{
  const auto found = goto_functions.function_map.find(fun);
  if(found == goto_functions.function_map.end())
    return;
  if(!found->second.body_available())
    return;

  const goto_programt::instructionst &instructions =
    found->second.body.instructions;
  if(instructions.size() == 0)
    return;

  for(const auto &ins : instructions)
  {
    if(ins.code.source_location().is_nil())
      continue;
    else if(!ins.code.source_location().is_built_in() && !is_entry_point)
    {
      std::string full_path = concat_dir_file(
        id2string(ins.code.source_location().get_working_directory()),
        id2string(ins.code.source_location().get_file()));
      std::unordered_set<std::string> &bucket = accumulator[full_path];
      bucket.insert(id2string(fun));
      fast_lookup.insert(fun);
      break;
    }
    else if(!is_entry_point)
      return;
  }

  if(level == 0U)
    return;

  std::size_t new_level = level == NO_LIMIT ? NO_LIMIT : level - 1;

  for(const auto &ins : instructions)
  {
    if(ins.code.get_statement() != ID_function_call)
      continue;
    const code_function_callt &call = to_code_function_call(ins.code);
    const irep_idt &call_name = call.function().get_string("identifier");
    if(fast_lookup.find(call_name) == fast_lookup.end())
      find_funs_to_search(
        new_level, call_name, false, fast_lookup, accumulator);
  }
}

void dispatch_loop_detectort::get_call_map(
  const std::unordered_set<irep_idt, irep_id_hash> &functions,
  std::unordered_map<std::string, std::unordered_map<std::size_t, std::string>>
    &call_map)
{
  for(const auto &fun : functions)
  {
    const auto &program = goto_functions.function_map.find(fun);
    INVARIANT(
      program != goto_functions.function_map.end(),
      "fun was one of the functions taken from the function_map in "
      "find_funs_to_search()");

    auto &function_map = call_map[fun.c_str()];
    forall_goto_program_instructions(ins, program->second.body)
    {
      if(!ins->is_function_call())
        continue;

      const source_locationt &loc = ins->source_location.is_nil()
                                      ? ins->code.source_location()
                                      : ins->source_location;
      if(loc.is_nil())
        continue;

      const code_function_callt &call = to_code_function_call(ins->code);
      if(call.function().is_nil())
        continue;
      const irep_idt &call_name_irep = call.function().get("identifier");
      const std::string call_name(call_name_irep.c_str());

      const auto found = functions.find(call_name);
      if(found == functions.end())
        continue;

      function_map.insert({std::stol(loc.get_line().c_str()), call_name});
    }
  }
}

void dispatch_loop_detectort::add_call_edges(
  const std::unordered_map<std::size_t, std::string> &call_map,
  const std::map<std::string, block_nodet::node_indext> &fun2idx,
  const block_nodet::node_indext &idx,
  std::set<block_nodet::node_indext> &seen)
{
  INVARIANT(
    graph[idx].type != block_nodet::typet::SWITCH_CASE,
    "SWITCH_CASES should have been converted to BRANCHes");
  INVARIANT(
    graph[idx].type != block_nodet::typet::DEAD,
    "DEAD nodes must not be descendants of functions, but add_call_edge "
    "was called on a FUNCTION node at the top-level");

  if(seen.find(idx) != seen.end())
    return;
  seen.insert(idx);

  if(
    graph[idx].line_begin == graph[idx].NO_LINE ||
    graph[idx].line_end == graph[idx].NO_LINE)
  {
    for(const auto &child : graph.get_successors(idx))
      add_call_edges(call_map, fun2idx, child, seen);
    return;
  }

  for(const auto &pair : call_map)
  {
    if(pair.first < graph[idx].line_begin)
      continue;
    if(pair.first > graph[idx].line_end)
      continue;
    bool called_by_a_child = false;
    for(const auto &child : graph.get_successors(idx))
      if(
        pair.first >= graph[child].line_begin &&
        pair.first <= graph[child].line_end)
      {
        called_by_a_child = true;
        break;
      }
    if(called_by_a_child)
      continue;
    graph.add_edge(idx, fun2idx.at(pair.second));
  }
  for(const auto &child : graph.get_successors(idx))
    add_call_edges(call_map, fun2idx, child, seen);
}

void dispatch_loop_detectort::get_indicies_of_all_nodes(
  const std::map<std::string, block_nodet::node_indext> &fun2idx,
  std::set<block_nodet::node_indext> &all_nodes)
{
  std::vector<block_nodet::node_indext> fun_indicies;
  fun_indicies.reserve(fun2idx.size());
  for(const auto &pair : fun2idx)
    fun_indicies.push_back(pair.second);
  std::vector<block_nodet::node_indext> tmp =
    graph.get_reachable(fun_indicies, true);
  all_nodes.insert(tmp.begin(), tmp.end());
}

void dispatch_loop_detectort::add_transitive_lines_to_branches(
  const lines2linest &lines2lines,
  const std::set<block_nodet::node_indext> &all_nodes)
{
  // lines2lines has one key for every LOC in the program, while all_nodes is
  // only a subset of the source locations. So only pass through lines2lines
  // once, and pass through all_nodes during the inner loop.
  for(const auto &pair : lines2lines)
  {
    const std::size_t current_line =
      safe_string2size_t(pair.first.get_line().c_str());
    const std::string current_file = concat_dir_file(
      id2string(pair.first.get_working_directory()),
      id2string(pair.first.get_file()));
    for(const auto &idx : all_nodes)
    {
      if(
        graph[idx].line_begin <= graph[idx].line_end &&
        graph[idx].line_begin <= current_line &&
        graph[idx].line_end >= current_line && graph[idx].file == current_file)
      {
        graph[idx].transitive_lines.insert(
          pair.second.begin(), pair.second.end());
      }
    }
  }
}

void dispatch_loop_detectort::compute_disjointness(
  const std::set<block_nodet::node_indext> &all_nodes)
{
  block_nodet::node_indext champion = -1;
  double champion_score = std::numeric_limits<double>::min();
  for(const auto &decision : all_nodes)
  {
    if(graph[decision].type != block_nodet::typet::DECISION)
      continue;
    const std::vector<block_nodet::node_indext> succs =
      graph.get_successors(decision);
    std::map<source_locationt, std::size_t> freqs;
    graph[decision].transitive_lines.clear();
    for(const auto &succ : succs)
      for(const auto &loc : graph[succ].transitive_lines)
      {
        ++freqs[loc];
        graph[decision].transitive_lines.insert(loc);
      }
    // inv_freq[i] shall contain all locs that appear in i+1 branches
    std::vector<std::set<source_locationt>> inv_freq(succs.size());
    for(const auto &pair : freqs)
      inv_freq[pair.second - 1].insert(pair.first);

    // Thanks to Benjamin Kaminski for this idea: calculate the expected number
    // of sets that an element ought to be a member of
    double expected = 0;
    for(std::size_t i = 0; i < inv_freq.size(); ++i)
      expected += inv_freq[i].size() * (i + 1);
    expected /= graph[decision].transitive_lines.size();

    graph[decision].disjointness = 1 - (expected - 1) / (inv_freq.size() - 1.0);

    graph[decision].score =
      graph[decision].disjointness * graph[decision].transitive_lines.size();

    if(graph[decision].score > champion_score)
    {
      champion = decision;
      champion_score = graph[decision].score;
    }

    log.debug() << "Disjointness of " << std::setprecision(6)
                << graph[decision].disjointness << " with "
                << graph[decision].transitive_lines.size()
                << " unique locs. Expecting " << expected
                << " sets per element." << log.eom;
    for(std::size_t i = 0; i < inv_freq.size(); ++i)
      log.debug() << "  Locs in " << i + 1 << " branches:" << inv_freq[i].size()
                  << log.eom;
  }

  if(champion != -1)
  {
    graph[champion].champion = true;
    optionalt<goto_programt> function_of_branches;
    make_dispatch_branches_into_champions(champion);
  }
}

void dispatch_loop_detectort::make_dispatch_branches_into_champions(
  const block_nodet::node_indext &decision_idx)
{
  const std::vector<block_nodet::node_indext> succs =
    graph.get_successors(decision_idx);
  INVARIANT(
    succs.size() > 0,
    "Dispatch decision should contain at least a single successor");
  std::size_t first_branch = std::numeric_limits<std::size_t>::max();
  for(std::size_t i = 0; i < succs.size(); ++i)
    if(graph[succs[i]].type == block_nodet::typet::BRANCH)
    {
      first_branch = i;
      break;
    }
  INVARIANT(
    first_branch != std::numeric_limits<std::size_t>::max(),
    "Dispatch decision should contain at least a single branch");

  const std::string &file = graph[succs[first_branch]].file;
  std::size_t lowest = graph[succs[first_branch]].line_begin;
  std::size_t highest = graph[succs[first_branch]].line_end;
  for(const auto &succ : succs)
  {
    if(graph[succ].type != block_nodet::typet::BRANCH)
      continue;
    graph[succ].champion = true;
    INVARIANT(
      graph[succ].file == file,
      "Every branch of the dispatch loop decision should be in the same file. "
      "Found one branch in file '" +
        graph[succ].file +
        "' and another in file "
        "'" +
        file + "'.");
    if(graph[succ].line_begin < lowest)
      lowest = graph[succ].line_begin;
    if(graph[succ].line_end > highest)
      highest = graph[succ].line_end;
  }

  // We now know which file contains the dispatch decision, and we know the
  // lowest and highest lines of its branches. Now we can find the function
  // (goto_programt) that contains the code for the dispatch function, and
  // associate each branch with the GOTO goto-instruction whose line number it
  // matches---only bothering to iterate through the instructions of a single
  // goto_program and avoiding goto_programs whose line numbers don't match.
  goto_functionst::function_mapt::const_iterator found =
    goto_functions.function_map.end();
  forall_goto_functions(f_it, goto_functions)
  {
    if(!f_it->second.body_available())
      continue;
    const std::vector<goto_programt::instructiont> instructions(
      f_it->second.body.instructions.begin(),
      f_it->second.body.instructions.end());
    if(instructions.size() == 0)
      continue;

    source_locationt first = sloc_of(instructions[0]);
    source_locationt last = sloc_of(instructions[0]);
    std::size_t i = 0;
    for(/* i in outer scope */; i < instructions.size(); ++i)
    {
      first = sloc_of(instructions[i]);
      if(first.is_not_nil())
        break;
    }

    if(first.is_nil())
      continue;
    if(std::stol(first.get_line().c_str()) > lowest)
      continue;
    for(/* i in outer scope */; i < instructions.size(); ++i)
    {
      source_locationt &tmp = sloc_of(instructions[i]);
      if(tmp.is_not_nil())
        last = tmp;
    }
    if(last.is_nil())
      continue;
    if(std::stol(last.get_line().c_str()) <= lowest)
      continue;

    INVARIANT(
      std::stol(last.get_line().c_str()) >= highest,
      "Found a goto-function '" + std::string(f_it->first.c_str()) +
        "' in file '" + file + "' that begins on line " +
        first.get_line().c_str() +
        ", which is before the line number of the "
        "lexicographically first branch in a decision (line " +
        std::to_string(lowest) + "); but the last line (" +
        last.get_line().c_str() +
        ") of the function is after the first branch, "
        "but _before_ the last branch (which is on line " +
        std::to_string(highest) +
        "). The function's last line should be after "
        "the line number of the last branch");
    found = f_it;
    break;
  }

  INVARIANT(
    found != goto_functions.function_map.end(),
    "Did not find a single goto-function in the file '" + file +
      "' that "
      "contains instructions from line numbers " +
      std::to_string(lowest) + "--" + std::to_string(highest));

  forall_goto_program_instructions(ins, found->second.body)
  {
    if(!ins->is_goto())
      continue;
    if(ins->guard.is_true())
      continue;
    const source_locationt &loc = sloc_of(ins);
    if(loc.is_nil())
      continue;

    for(const auto &succ : succs)
    {
      if(
        graph[succ].line_begin <= std::stol(loc.get_line().c_str()) &&
        graph[succ].line_end >= std::stol(loc.get_line().c_str()))
      {
        // Assign the instruction with the matching line number which has the
        // _lowest_ location number.
        if(
          graph[succ].has_goto_instruction() &&
          ins->location_number >
            graph[succ].goto_instruction()->location_number)
        {
          continue;
        }
        graph[succ]._goto_instruction = ins;
        break;
      }
    }
  }
}

int dispatch_loop_detectort::distance_to_champion_descendants(
  const grapht<block_nodet>::node_indext &idx,
  const int distance,
  std::unordered_set<grapht<block_nodet>::node_indext> &seen)
{
  if(distance == 0)
    return std::numeric_limits<int>::max();
  if(seen.find(idx) != seen.end())
    return std::numeric_limits<int>::max();
  seen.insert(idx);
  const std::size_t new_distance = distance - 1;
  int closest_loop = std::numeric_limits<int>::max();
  for(const auto &succ : graph.get_successors(idx))
  {
    if(graph[succ].champion)
      return 1;
    else if(graph[succ].type == block_nodet::typet::LOOP)
      continue;
    else
    {
      int succ_distance =
        distance_to_champion_descendants(succ, new_distance, seen);
      if(
        succ_distance != std::numeric_limits<int>::max() &&
        succ_distance + 1 < closest_loop)
      {
        closest_loop = succ_distance + 1;
      }
    }
  }
  return closest_loop;
}

bool dispatch_loop_detectort::find_dispatch_loop(
  const std::set<block_nodet::node_indext> &all_nodes)
{
  grapht<block_nodet>::node_indext closest_loop;
  int closest_loop_distance = std::numeric_limits<int>::max();
  for(const auto &loop : all_nodes)
  {
    if(graph[loop].type != block_nodet::typet::LOOP)
      continue;
    std::unordered_set<grapht<block_nodet>::node_indext> seen;
    int distance =
      distance_to_champion_descendants(loop, loop_decision_distance, seen);
    if(
      distance != std::numeric_limits<int>::max() &&
      distance < closest_loop_distance)
    {
      closest_loop_distance = distance;
      closest_loop = loop;
    }
  }

  if(closest_loop_distance == std::numeric_limits<int>::max())
  {
    log.status() << "Could not find dispatch loop node" << log.eom;
    return true;
  }

  log.debug() << "Closest loop is at file " << graph[closest_loop].file
              << " line " << graph[closest_loop].line_begin << log.eom;

  // Identify the goto program instruction that corresponds to this loop, using
  // Clang's version of `closest_loop`'s location.

  goto_programt::const_targett first_instruction;
  goto_programt::const_targett subsequent_instruction;
  std::set<goto_programt::const_targett> loop_set;
  std::size_t lowest_line = std::numeric_limits<std::size_t>::max();

  forall_goto_functions(f_it, goto_functions)
  {
    natural_loopst natural_loop;
    natural_loop(f_it->second.body);
    forall_goto_program_instructions(ins, f_it->second.body)
    {
      const source_locationt &current_loc =
        ins->code.source_location().is_not_nil() ? ins->code.source_location()
                                                 : ins->source_location;
      if(current_loc.is_nil())
        continue;

      std::string ins_path = concat_dir_file(
        id2string(current_loc.get_working_directory()),
        id2string(current_loc.get_file()));
      if(ins_path != graph[closest_loop].file)
        continue;

      // Find the natural loop whose head line number is the lowest line
      // less than or equal to the line that Clang reports as being the
      // beginning of the loop.
      for(const auto &pair : natural_loop.loop_map)
      {
        const source_locationt &loop_head_loc =
          pair.first->code.source_location().is_not_nil()
            ? pair.first->code.source_location()
            : pair.first->source_location;
        if(loop_head_loc.is_nil())
          continue;
        const std::size_t loop_head_line =
          std::stol(loop_head_loc.get_line().c_str());
        if(
          loop_head_line >= graph[closest_loop].line_begin &&
          loop_head_line < lowest_line)
        {
          lowest_line = loop_head_line;
          first_instruction = pair.first;
          loop_set = pair.second;
        }
      }
    }
  }

  if(lowest_line == std::numeric_limits<std::size_t>::max())
  {
    log.warning() << "Identified dispatch loop (LOC '"
                  << graph[closest_loop].label << "', file '"
                  << graph[closest_loop].file << "', lines "
                  << graph[closest_loop].line_begin << "-"
                  << graph[closest_loop].line_end << ") but could not find a "
                  << "matching goto-program instruction." << log.eom;
    return true;
  }
  else
  {
    log.debug() << "Identified instruction of dispatch loop as "
                << first_instruction->source_location.as_string() << log.eom;
    graph[closest_loop].champion = true;
    graph[closest_loop]._first_instruction = first_instruction;
    find_subsequent_instruction(closest_loop, loop_set);
    return false;
  }
}

void dispatch_loop_detectort::find_subsequent_instruction(
  const block_nodet::node_indext &dispatch_loop_index,
  const std::set<goto_programt::const_targett> &loop_set)
{
  std::list<goto_programt::const_targett> locs_in_loop(
    loop_set.begin(), loop_set.end());
  locs_in_loop.sort([](
                      const goto_programt::const_targett &i1,
                      const goto_programt::const_targett &i2) {
    return i1->location_number < i2->location_number;
  });

  goto_programt::const_targett &first = *locs_in_loop.begin();
  while(!first->is_goto() && first->type != END_FUNCTION)
    first = std::next(first);

  goto_programt::const_targett &last = *std::prev(locs_in_loop.end());
  while(!last->is_goto())
    if(last == first)
      break;
    else
      last = std::prev(last);

  bool found = false;
  for(auto &ins : {first, last})
  {
    if(!ins->is_goto())
      continue;
    if(ins->guard.is_true())
      continue;
    INVARIANT(
      ins->has_target(),
      "`ins` is a conditional goto and should therefore have a target");
    if(ins == first)
    {
      goto_programt::const_targett maybe_guard = ins->get_target();
      if(loop_set.find(maybe_guard) != loop_set.end())
        // This GOTO instruction is at the beginning of the loop, but its target
        // is something _inside_ the loop---not the instruction after the loop.
        // So it cannot be the loop guard. Continue, maybe the loop guard is the
        // last instruction of the loop rather than the first.
        continue;
      else
      {
        graph[dispatch_loop_index]._subsequent_instruction = maybe_guard;
        found = true;
        break;
      }
    }
    else
    {
      INVARIANT(
        loop_set.find(ins->get_target()) != loop_set.end(),
        "The last instruction in a loop should have a target inside the "
        "loop if it is the loop's guard");
      INVARIANT(
        ins->location_number > ins->get_target()->location_number,
        "The last instruction in a loop should have a target that is "
        "lexicographically before it if the instruction is a loop guard. "
        "We think the last instruction in the loop has location # " +
          std::to_string(ins->location_number) +
          " and its target has "
          "location # " +
          std::to_string(ins->get_target()->location_number));
      goto_programt::const_targett tmp = std::next(ins);
      graph[dispatch_loop_index]._subsequent_instruction = tmp;
      found = true;
      break;
    }
  }
  INVARIANT(
    found,
    "There should always be an instruction following a loop; did not find "
    "an instruction following the loop at location number " +
      std::to_string(first->location_number) + " whose last location is at " +
      std::to_string(last->location_number));
  INVARIANT(
    loop_set.find(graph[dispatch_loop_index].subsequent_instruction()) ==
      loop_set.end(),
    "The instruction following the loop should not be in the loop. We "
    "think the instruction following the loop is :" +
      graph[dispatch_loop_index].subsequent_instruction()->code.pretty());
}

bool dispatch_loop_detectort::block_nodet::is_function(
  const std::string &fun_name) const
{
  return type == typet::FUNCTION && label == fun_name;
}

bool dispatch_loop_detectort::block_nodet::
operator==(const block_nodet &other) const
{
  return type == other.type && transitive_lines == other.transitive_lines;
}

std::string dispatch_loop_detectort::block_nodet::dot_attributes(
  const node_indext &idx) const
{
  if(type == typet::DEAD)
    return R"([color="white",style="filled",fontcolor="white"])";

  std::stringstream ss;
  ss << std::to_string(idx) << " [shape=\"" << shape() << "\", "
     << "label=\"" << std::to_string(idx) << ": " << text() << "\", "
     << "style=\"filled\", "
     << "color=\"" << colour() << "\", "
     << "]";

  return ss.str();
}

inline std::string dispatch_loop_detectort::block_nodet::text() const
{
  std::stringstream ss;
  ss << label;
  if(type == typet::FUNCTION)
    ss << "()\\nfile: " << file;
  if(line_begin != NO_LINE)
  {
    ss << "\\nlines " << line_begin << "--";
    if(line_end != NO_LINE)
      ss << line_end;
  }

  if(type == typet::BRANCH)
  {
    ss << ", touches " << transitive_lines.size() << " lines";
    if(champion && has_goto_instruction())
      ss << "\\nGOTO is at location #" << goto_instruction()->location_number;
  }
  else if(type == typet::FUNCTION)
    ss << " (" << line_end - line_begin << " lines long)";
  else if(type == typet::DECISION && disjointness <= 1.0)
  {
    ss << " (disjointness: " << std::setprecision(4) << disjointness << " over "
       << transitive_lines.size() << " unique lines"
       << ".";
    if(champion)
      ss << " Score: " << score << ")";
    else
      ss << ")";
  }
  else if(type == typet::LOOP && champion)
  {
    if(has_first_instruction())
      ss << "\\nFirst instruction is at location #"
         << first_instruction()->location_number;
    if(has_subsequent_instruction())
      ss << "\\nSubsequent instruction is at location #"
         << subsequent_instruction()->location_number;
  }

  return ss.str();
}

inline std::string dispatch_loop_detectort::block_nodet::colour() const
{
  switch(type)
  {
  case typet::LOOP:
    if(champion)
      return "#d84315";
    else
      return "#ffccbc";
  case typet::DECISION:
    if(champion)
      return "#42a5f5";
    else
      return "#bbdefb";
  case typet::BRANCH:
    return "#d7ccc8";
  case typet::FUNCTION:
    return "#f8bbd0";

  // Nodes should not have these types by the time the graph is completely
  // constructed. I'm leaving these cases in so that people can dump the graph
  // while it's still being constructed, for debugging.
  case typet::DUNNO:
    return "#f5f5f5";
  case typet::SWITCH_CASE:
    return "#bdbdbd";
  default:
    UNREACHABLE;
  }
  UNREACHABLE;
}

inline std::string dispatch_loop_detectort::block_nodet::shape() const
{
  switch(type)
  {
  case typet::LOOP:
    return "egg";
  case typet::DECISION:
    return "diamond";
  case typet::BRANCH:
    return "box";
  case typet::FUNCTION:
    return "house";

  // Nodes should not have these types by the time the graph is completely
  // constructed. I'm leaving these cases in so that people can dump the graph
  // while it's still being constructed, for debugging.
  case typet::DUNNO:
    return "none";
  case typet::SWITCH_CASE:
    return "diamond";
  default:
    UNREACHABLE;
  }
  UNREACHABLE;
}

std::string dispatch_loop_detectort::get_line_of_file(
  const std::string &file_name,
  const std::size_t line_number) const
{
  auto found = source_code.find(file_name);
  if(found == source_code.end())
    return "<unknown>";
  if(line_number > found->second.size())
    return "<unknown>";
  std::string ret = found->second[line_number - 1];
  for(const auto &pair : line_replacements)
    ret = std::regex_replace(ret, pair.first, pair.second);
  return ret;
}

void dispatch_loop_detectort::read_source_code(
  const std::unordered_map<std::string, std::unordered_set<std::string>> &files)
{
  for(const auto &pair : files)
  {
    std::vector<std::string> &lines = source_code[pair.first];
    std::ifstream inf(pair.first);
    std::string tmp;
    while(std::getline(inf, tmp))
      lines.push_back(tmp);
    inf.close();
  }
}

dispatch_loop_detectort::block_nodet::block_nodet()
  : type(typet::DUNNO),
    label("<unknown>"),
    file("<unknown>"),
    NO_LINE(std::numeric_limits<std::size_t>::max()),
    line_begin(NO_LINE),
    line_end(NO_LINE),
    NOT_CALCULATED(std::numeric_limits<double>::max()),
    disjointness(NOT_CALCULATED),
    score(NOT_CALCULATED),
    champion(false)
{
}

void dispatch_loop_detectort::block_nodet::init(
  const typet _type,
  const std::string &_label,
  const std::string &_file,
  const std::size_t _line_begin,
  const std::size_t _line_end)
{
  type = _type;
  label = _label;
  file = _file;
  line_begin = _line_begin;
  line_end = _line_end;
}

dispatch_loop_detectort::dispatch_loopt::dispatch_loopt(
  const dispatch_loop_detectort &dld)
  : goto_functions(dld.goto_functions),
    graph(dld.graph),
    log(dld.log),
    members(build_members())
{
}

dispatch_loop_detectort::dispatch_loopt::memberst
dispatch_loop_detectort::dispatch_loopt::build_members() const
{
  std::forward_list<block_nodet::node_indext> all_nodes;
  get_all_nodes(all_nodes);

  optionalt<goto_programt::const_targett> first_instruction;
  optionalt<goto_programt::const_targett> subsequent_instruction;
  std::set<goto_programt::const_targett> cases;

  for(const auto &node : all_nodes)
  {
    if(!first_instruction && graph[node].type == block_nodet::typet::LOOP)
      try_assigning_first_and_subsequent(
        node, first_instruction, subsequent_instruction);
    else if(
      graph[node].type == block_nodet::typet::BRANCH && graph[node].champion &&
      graph[node].has_goto_instruction())
    {
      cases.insert(graph[node].goto_instruction());
    }
  }

  INVARIANT(
    first_instruction,
    "An instruction corresponding to a dispatch loop was not found in the "
    "goto program. dispatch_loop_detectort::dispatch_loopt should only be "
    "constructed from a graph created by a dispatch_loop_detectort whose "
    "detech_dispatch_loops() function returns `false`.");

  INVARIANT(
    subsequent_instruction,
    "The first instruction after the end of the dispatch loop should have "
    "been set in the same call to `try_assigning_first_and_subsequent()` that "
    "successfully set `first_instruction`.");

  return std::make_tuple(*first_instruction, cases, *subsequent_instruction);
}

void dispatch_loop_detectort::dispatch_loopt::
  try_assigning_first_and_subsequent(
    const block_nodet::node_indext &loop_node,
    optionalt<goto_programt::const_targett> &first_instruction,
    optionalt<goto_programt::const_targett> &subsequent_instruction) const
{
  if(!graph[loop_node].champion)
    return;

  INVARIANT(
    !first_instruction,
    "There should only be a single instruction in the program corresponding "
    "to the dispatch loop in the graph. Found the following two instructions:"
    "\n" +
      (*first_instruction)->code.pretty() + "\n\nand\n\n" +
      graph[loop_node].first_instruction()->code.pretty());

  INVARIANT(
    !subsequent_instruction,
    "There should only be a single instruction in the program corresponding "
    "to the instruction after the dispatch loop in the graph. Found the "
    "following two instructions:"
    "\n" +
      (*subsequent_instruction)->code.pretty() + "\n\nand\n\n" +
      graph[loop_node].subsequent_instruction()->code.pretty());

  first_instruction = graph[loop_node].first_instruction();
  subsequent_instruction = graph[loop_node].subsequent_instruction();
}

bool dispatch_loop_detectort::dispatch_loopt::lines_match(
  const block_nodet::node_indext &node,
  const goto_programt::const_targett &ins) const
{
  const source_locationt &current_location =
    ins->code.source_location().is_not_nil() ? ins->code.source_location()
                                             : ins->source_location;
  if(current_location.is_nil())
    return false;
  std::string ins_path = concat_dir_file(
    id2string(current_location.get_working_directory()),
    id2string(current_location.get_file()));
  if(ins_path != graph[node].file)
    return false;

  std::size_t ins_line = std::stol(current_location.get_line().c_str());
  if(ins_line != graph[node].line_begin)
    return false;

  return true;
}

void dispatch_loop_detectort::dispatch_loopt::get_all_nodes(
  std::forward_list<dispatch_loop_detectort::block_nodet::node_indext>
    &all_nodes) const
{
  for(grapht<block_nodet>::node_indext i = 0; i < graph.size(); ++i)
  {
    switch(graph[i].type)
    {
    case block_nodet::typet::FUNCTION:
    case block_nodet::typet::LOOP:
    case block_nodet::typet::DECISION:
    case block_nodet::typet::BRANCH:
      all_nodes.push_front(i);
      break;
    case block_nodet::typet::DUNNO:
    case block_nodet::typet::DEAD:
      break;
    case block_nodet::typet::SWITCH_CASE:
      INVARIANT(false, "SWITCH_CASEs should have been converted to BRANCHes");
    }
  }
}

void dispatch_loop_detectort::set_front_end_options(
  const cmdlinet &cmdline,
  optionst &opts)
{
  if(cmdline.isset("dispatch-function-search-depth"))
  {
    opts.set_option(
      "dispatch-function-search-depth",
      std::stoi(cmdline.get_value("dispatch-function-search-depth")));
  }

  if(cmdline.isset("dispatch-loop-decision-distance"))
  {
    opts.set_option(
      "dispatch-loop-decision-distance",
      std::stoi(cmdline.get_value("dispatch-loop-decision-distance")));
  }
}
