/*******************************************************************\

Module: Control Flow Graph

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Control Flow Graph

#ifndef CPROVER_GOTO_PROGRAMS_CFG_H
#define CPROVER_GOTO_PROGRAMS_CFG_H

#include <util/dense_integer_map.h>
#include <util/graph.h>
#include <util/std_expr.h>

#include "goto_functions.h"

class empty_cfg_nodet
{
};

// these are the CFG nodes
template<class T, typename I>
struct cfg_base_nodet:public graph_nodet<empty_edget>, public T
{
  typedef typename graph_nodet<empty_edget>::edget edget;
  typedef typename graph_nodet<empty_edget>::edgest edgest;

  I PC;
};

/// Functor to convert cfg nodes into dense integers, used by \ref cfg_baset.
/// Default implementation: the identity function.
template <class T>
class cfg_instruction_to_dense_integert
{
public:
  template <class U>
  std::size_t operator()(U &&u) const
  {
    return std::forward<U>(identity_functort{}(u));
  }
};

/// GOTO-instruction to location number functor.
template <>
class cfg_instruction_to_dense_integert<goto_programt::const_targett>
{
public:
  std::size_t operator()(const goto_programt::const_targett &t) const
  {
    return t->location_number;
  }
};

/// A multi-procedural control flow graph (CFG) whose nodes store references to
/// instructions in a GOTO program.
///
/// An instance of cfg_baset<T> is a directed graph whose nodes inherit from a
/// user-provided type T and store a pointer to an instruction of some
/// goto program in the field `PC`. The field `PC` of every node points to the
/// original GOTO instruction that gave rise to the node, and the field
/// cfg_baset::entry_map maps every GOTO instruction to some CFG node.
///
/// The CFG is constructed on the operator() from either one goto_programt or
/// multiple goto_programt objects (stored in a goto_functionst).  The edges of
/// the CFG are created on the method compute_edges(), and notably include:
///
/// - Edges from location A to B if both A and B belong to the same
///   goto_programt and A can flow into B.
/// - An edge from each FUNCTION_CALL instruction and the first instruction of
///   the called function, when that function body is available and its body is
///   non-empty.
/// - For each FUNCTION_CALL instruction found, an edge between the exit point
///   of the called function and the instruction immediately after the
///   FUNCTION_CALL, when the function body is available and its body is
///   non-empty.
///
///   Note that cfg_baset is the base class of many other subclasses and the
///   specific edges constructed by operator() can be different in those.
template<class T,
         typename P=const goto_programt,
         typename I=goto_programt::const_targett>
class cfg_baset:public grapht< cfg_base_nodet<T, I> >
{
  typedef grapht<cfg_base_nodet<T, I>> base_grapht;

public:
  typedef typename base_grapht::node_indext entryt;
  typedef typename base_grapht::nodet nodet;

  class entry_mapt final
  {
    typedef dense_integer_mapt<
      goto_programt::const_targett,
      entryt,
      cfg_instruction_to_dense_integert<goto_programt::const_targett>>
      data_typet;
    data_typet data;

  public:
    grapht< cfg_base_nodet<T, I> > &container;

    explicit entry_mapt(grapht< cfg_base_nodet<T, I> > &_container):
      container(_container)
    {
    }

    entryt &operator[](const goto_programt::const_targett &t)
    {
      auto e=data.insert(std::make_pair(t, 0));

      if(e)
        data.at(t) = container.add_node();

      return data.at(t);
    }

    entryt &at(const goto_programt::const_targett &t)
    {
      return data.at(t);
    }
    const entryt &at(const goto_programt::const_targett &t) const
    {
      return data.at(t);
    }

    std::size_t count(const goto_programt::const_targett &t) const
    {
      return data.count(t);
    }

    typedef typename data_typet::possible_keyst keyst;
    const keyst &keys() const
    {
      // We always define exactly the keys the entry map was set up for, so
      // data's possible key set is exactly our key set
      return data.possible_keys();
    }

    template <class Iter>
    void setup_for_keys(Iter begin, Iter end)
    {
      data.setup_for_keys(begin, end);
    }
  };
  entry_mapt entry_map;

protected:
  virtual void compute_edges_goto(
    const goto_programt &goto_program,
    const goto_programt::instructiont &instruction,
    goto_programt::const_targett next_PC,
    entryt &entry);

  virtual void compute_edges_catch(
    const goto_programt &goto_program,
    const goto_programt::instructiont &instruction,
    goto_programt::const_targett next_PC,
    entryt &entry);

  virtual void compute_edges_throw(
    const goto_programt &goto_program,
    const goto_programt::instructiont &instruction,
    goto_programt::const_targett next_PC,
    entryt &entry);

  virtual void compute_edges_start_thread(
    const goto_programt &goto_program,
    const goto_programt::instructiont &instruction,
    goto_programt::const_targett next_PC,
    entryt &entry);

  virtual void compute_edges_function_call(
    const goto_functionst &goto_functions,
    const goto_programt &goto_program,
    const goto_programt::instructiont &instruction,
    goto_programt::const_targett next_PC,
    entryt &entry);

  void compute_edges(
    const goto_functionst &goto_functions,
    const goto_programt &goto_program,
    I PC);

  void compute_edges(
    const goto_functionst &goto_functions,
    P &goto_program);

  void compute_edges(
    const goto_functionst &goto_functions);

public:
  cfg_baset():entry_map(*this)
  {
  }

  virtual ~cfg_baset()
  {
  }

  void operator()(
    const goto_functionst &goto_functions)
  {
    std::vector<goto_programt::const_targett> possible_keys;
    for(const auto &id_and_function : goto_functions.function_map)
    {
      const auto &instructions = id_and_function.second.body.instructions;
      possible_keys.reserve(
        possible_keys.size() +
        std::distance(instructions.begin(), instructions.end()));
      for(auto it = instructions.begin(); it != instructions.end(); ++it)
        possible_keys.push_back(it);
    }
    entry_map.setup_for_keys(possible_keys.begin(), possible_keys.end());
    compute_edges(goto_functions);
  }

  void operator()(P &goto_program)
  {
    goto_functionst goto_functions;
    std::vector<goto_programt::const_targett> possible_keys;
    const auto &instructions = goto_program.instructions;
    possible_keys.reserve(
      std::distance(instructions.begin(), instructions.end()));
    for(auto it = instructions.begin(); it != instructions.end(); ++it)
      possible_keys.push_back(it);
    entry_map.setup_for_keys(possible_keys.begin(), possible_keys.end());
    compute_edges(goto_functions, goto_program);
  }

  /// Get the graph node index for \p program_point. Use this with operator[]
  /// to get the related graph node (e.g. `cfg[cfg.get_node_index(i)]`, though
  /// in that particular case you should just use `cfg.get_node(i)`). Storing
  /// node indices saves a map lookup, so it can be worthwhile when you expect
  /// to repeatedly look up the same program point.
  entryt get_node_index(const goto_programt::const_targett &program_point) const
  {
    return entry_map.at(program_point);
  }

  /// Get the CFG graph node relating to \p program_point.
  nodet &get_node(const goto_programt::const_targett &program_point)
  {
    return (*this)[get_node_index(program_point)];
  }

  /// Get the CFG graph node relating to \p program_point.
  const nodet &get_node(const goto_programt::const_targett &program_point) const
  {
    return (*this)[get_node_index(program_point)];
  }

  /// Get a vector of keys present in this cfg. Use these with \ref get_node or
  /// \ref get_node_index to get the corresponding CFG nodes.
  const typename entry_mapt::keyst &keys() const
  {
    return entry_map.keys();
  }

  static I get_first_node(P &program)
  {
    return program.instructions.begin();
  }
  static I get_last_node(P &program)
  {
    return --program.instructions.end();
  }
  static bool nodes_empty(P &program)
  {
    return program.instructions.empty();
  }
};

template<class T,
         typename P=const goto_programt,
         typename I=goto_programt::const_targett>
class concurrent_cfg_baset:public virtual cfg_baset<T, P, I>
{
protected:
  virtual void compute_edges_start_thread(
    const goto_programt &goto_program,
    const goto_programt::instructiont &instruction,
    goto_programt::const_targett next_PC,
    typename cfg_baset<T, P, I>::entryt &entry);
};

template<class T,
         typename P=const goto_programt,
         typename I=goto_programt::const_targett>
class procedure_local_cfg_baset:public virtual cfg_baset<T, P, I>
{
protected:
  virtual void compute_edges_function_call(
    const goto_functionst &goto_functions,
    const goto_programt &goto_program,
    const goto_programt::instructiont &instruction,
    goto_programt::const_targett next_PC,
    typename cfg_baset<T, P, I>::entryt &entry);
};

template<class T,
         typename P=const goto_programt,
         typename I=goto_programt::const_targett>
class procedure_local_concurrent_cfg_baset:
  public concurrent_cfg_baset<T, P, I>,
  public procedure_local_cfg_baset<T, P, I>
{
};

template<class T, typename P, typename I>
void cfg_baset<T, P, I>::compute_edges_goto(
  const goto_programt &goto_program,
  const goto_programt::instructiont &instruction,
  goto_programt::const_targett next_PC,
  entryt &entry)
{
  if(
    next_PC != goto_program.instructions.end() &&
    !instruction.get_condition().is_true())
  {
    this->add_edge(entry, entry_map[next_PC]);
  }

  this->add_edge(entry, entry_map[instruction.get_target()]);
}

template<class T, typename P, typename I>
void cfg_baset<T, P, I>::compute_edges_catch(
  const goto_programt &goto_program,
  const goto_programt::instructiont &instruction,
  goto_programt::const_targett next_PC,
  entryt &entry)
{
  if(next_PC!=goto_program.instructions.end())
    this->add_edge(entry, entry_map[next_PC]);

  // Not ideal, but preserves targets
  // Ideally, the throw statements should have those as successors

  for(const auto &t : instruction.targets)
    if(t!=goto_program.instructions.end())
      this->add_edge(entry, entry_map[t]);
}

template<class T, typename P, typename I>
void cfg_baset<T, P, I>::compute_edges_throw(
  const goto_programt &,
  const goto_programt::instructiont &,
  goto_programt::const_targett,
  entryt &)
{
  // no (trivial) successors
}

template<class T, typename P, typename I>
void cfg_baset<T, P, I>::compute_edges_start_thread(
  const goto_programt &goto_program,
  const goto_programt::instructiont &,
  goto_programt::const_targett next_PC,
  entryt &entry)
{
  if(next_PC!=goto_program.instructions.end())
    this->add_edge(entry, entry_map[next_PC]);
}

template<class T, typename P, typename I>
void concurrent_cfg_baset<T, P, I>::compute_edges_start_thread(
  const goto_programt &goto_program,
  const goto_programt::instructiont &instruction,
  goto_programt::const_targett next_PC,
  typename cfg_baset<T, P, I>::entryt &entry)
{
  cfg_baset<T, P, I>::compute_edges_start_thread(
    goto_program,
    instruction,
    next_PC,
    entry);

  this->add_edge(entry, this->entry_map[instruction.get_target()]);
}

template<class T, typename P, typename I>
void cfg_baset<T, P, I>::compute_edges_function_call(
  const goto_functionst &goto_functions,
  const goto_programt &goto_program,
  const goto_programt::instructiont &instruction,
  goto_programt::const_targett next_PC,
  entryt &entry)
{
  const exprt &function = instruction.get_function_call().function();

  if(function.id()!=ID_symbol)
    return;

  const irep_idt &identifier=
    to_symbol_expr(function).get_identifier();

  goto_functionst::function_mapt::const_iterator f_it=
    goto_functions.function_map.find(identifier);

  if(f_it!=goto_functions.function_map.end() &&
     f_it->second.body_available())
  {
    // get the first instruction
    goto_programt::const_targett i_it=
      f_it->second.body.instructions.begin();

    goto_programt::const_targett e_it=
      f_it->second.body.instructions.end();

    goto_programt::const_targett last_it=e_it; last_it--;

    if(i_it!=e_it)
    {
      // nonempty function
      this->add_edge(entry, entry_map[i_it]);

      // add the last instruction as predecessor of the return location
      if(next_PC!=goto_program.instructions.end())
        this->add_edge(entry_map[last_it], entry_map[next_PC]);
    }
    else if(next_PC!=goto_program.instructions.end())
    {
      // empty function
      this->add_edge(entry, entry_map[next_PC]);
    }
  }
  else if(next_PC!=goto_program.instructions.end())
    this->add_edge(entry, entry_map[next_PC]);
}

template<class T, typename P, typename I>
void procedure_local_cfg_baset<T, P, I>::compute_edges_function_call(
  const goto_functionst &,
  const goto_programt &goto_program,
  const goto_programt::instructiont &instruction,
  goto_programt::const_targett next_PC,
  typename cfg_baset<T, P, I>::entryt &entry)
{
  const exprt &function = instruction.get_function_call().function();

  if(function.id()!=ID_symbol)
    return;

  if(next_PC!=goto_program.instructions.end())
    this->add_edge(entry, this->entry_map[next_PC]);
}

template<class T, typename P, typename I>
void cfg_baset<T, P, I>::compute_edges(
  const goto_functionst &goto_functions,
  const goto_programt &goto_program,
  I PC)
{
  const goto_programt::instructiont &instruction=*PC;
  entryt entry=entry_map[PC];
  (*this)[entry].PC=PC;
  goto_programt::const_targett next_PC(PC);
  next_PC++;

  // compute forward edges first
  switch(instruction.type)
  {
  case GOTO:
    compute_edges_goto(goto_program, instruction, next_PC, entry);
    break;

  case CATCH:
    compute_edges_catch(goto_program, instruction, next_PC, entry);
    break;

  case THROW:
    compute_edges_throw(goto_program, instruction, next_PC, entry);
    break;

  case START_THREAD:
    compute_edges_start_thread(
      goto_program,
      instruction,
      next_PC,
      entry);
    break;

  case FUNCTION_CALL:
    compute_edges_function_call(
      goto_functions,
      goto_program,
      instruction,
      next_PC,
      entry);
    break;

  case END_THREAD:
  case END_FUNCTION:
    // no successor
    break;

  case ASSUME:
    // false guard -> no successor
    if(instruction.get_condition().is_false())
      break;

  case ASSIGN:
  case ASSERT:
  case OTHER:
  case RETURN:
  case SKIP:
  case LOCATION:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
  case DECL:
  case DEAD:
    if(next_PC!=goto_program.instructions.end())
      this->add_edge(entry, entry_map[next_PC]);
    break;

  case NO_INSTRUCTION_TYPE:
  case INCOMPLETE_GOTO:
    UNREACHABLE;
    break;
  }
}

template<class T, typename P, typename I>
void cfg_baset<T, P, I>::compute_edges(
  const goto_functionst &goto_functions,
  P &goto_program)
{
  for(I it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      ++it)
    compute_edges(goto_functions, goto_program, it);
}

template<class T, typename P, typename I>
void cfg_baset<T, P, I>::compute_edges(
  const goto_functionst &goto_functions)
{
  forall_goto_functions(it, goto_functions)
    if(it->second.body_available())
      compute_edges(goto_functions, it->second.body);
}

template <class T, typename I>
struct basic_block_graph_nodet : public graph_nodet<empty_edget>, public T
{
  typedef typename graph_nodet<empty_edget>::edget edget;
  typedef typename graph_nodet<empty_edget>::edgest edgest;

  basic_block_graph_nodet() = default;
  explicit basic_block_graph_nodet(std::vector<I> &&block)
    : block(std::move(block))
  {
  }

  std::vector<I> block;
};

template <typename T>
struct constify_cfg_instruction_typet
{
  typedef T type;
};

template <>
struct constify_cfg_instruction_typet<goto_programt::targett>
{
  typedef goto_programt::const_targett type;
};

template <
  template <typename, typename, typename> class CFGT,
  typename T,
  typename P = const goto_programt,
  typename I = goto_programt::const_targett>
class cfg_basic_blockst : public grapht<basic_block_graph_nodet<T, I>>
{
public:
  typedef CFGT<empty_cfg_nodet, P, I> base_cfgt;
  typedef grapht<basic_block_graph_nodet<T, I>> graph_typet;
  typedef typename graph_typet::nodet nodet;
  typedef typename graph_typet::node_indext node_indext;
  typedef typename constify_cfg_instruction_typet<I>::type ConstI;
  typedef dense_integer_mapt<
    ConstI,
    node_indext,
    cfg_instruction_to_dense_integert<ConstI>>
    entry_mapt;
  entry_mapt entry_map;

  void operator()(P &program)
  {
    // Compute underlying program graph:
    base_cfgt base_cfg;
    base_cfg(program);

    if(base_cfg.empty())
      return;

    entry_map.setup_for_keys(base_cfg.keys().begin(), base_cfg.keys().end());

    std::vector<node_indext> worklist;
    // Queue all instructions without predecessors to start block construction:
    for(node_indext i = 0; i < base_cfg.size(); ++i)
      if(base_cfg[i].in.size() == 0)
        worklist.push_back(i);

    // Consider the entry-point, if not already added:
    auto entry_point_index = base_cfg.entry_map[get_first_node(program)];
    if(base_cfg[entry_point_index].in.size() != 0)
      worklist.push_back(entry_point_index);

    while(true)
    {
      // Extract basic blocks:
      while(!worklist.empty())
      {
        node_indext block_head = worklist.back();
        worklist.pop_back();
        std::vector<I> block = {base_cfg[block_head].PC};
        node_indext block_current = block_head;

        // Find other instructions in the same block:
        while(base_cfg[block_current].out.size() == 1)
        {
          node_indext block_next = base_cfg[block_current].out.begin()->first;
          // Note the successor instruction could already have a block if
          // (a) it is the entry point, which has an extra imaginary predecessor
          // due to control flow from another function, or (b) we're picking
          // up unreachable code and our arbitrarily picked starting point
          // fell in the middle of a basic block.
          if(
            base_cfg[block_next].in.size() == 1 &&
            !entry_map.count(base_cfg[block_next].PC))
          {
            // Part of the same basic block
            block.push_back(base_cfg[block_next].PC);
            block_current = block_next;
          }
          else
          {
            // Start of a new basic block
            break;
          }
        }

        // Store the new basic block:
        node_indext new_block_index = this->add_node(std::move(block));

        // Record the instruction -> block index mapping:
        for(const auto &instruction : (*this)[new_block_index].block)
        {
          auto insert_result = entry_map.insert({instruction, new_block_index});
          INVARIANT(
            insert_result,
            "should only visit each instruction once. Are the keys unique? "
            "If your key is goto_programt::targett, do you need to run "
            "goto_programt/functionst::update()?");
        }

        // Queue all the block tail's successors that we haven't visited yet:
        for(const auto successor_entry : base_cfg[block_current].out)
        {
          if(!entry_map.count(base_cfg[successor_entry.first].PC))
            worklist.push_back(successor_entry.first);
        }
      }

      // Check that we covered the whole CFG: if not then there are unreachable
      // cycles; pick one arbitrarily and try again.
      if(entry_map.size() == base_cfg.size())
        break;

      for(node_indext i = 0; i < base_cfg.size(); ++i)
      {
        if(!entry_map.count(base_cfg[i].PC))
        {
          worklist.push_back(i);
          break;
        }
      }

      INVARIANT(
        worklist.size() == 1,
        "if the entry-map is not fully populated there must be some missing "
        "instruction");
    }

    // Populate basic-block edges:
    for(node_indext block_index = 0; block_index < this->size(); ++block_index)
    {
      auto &block_node = (*this)[block_index];
      I block_tail = block_node.block.back();
      const auto &base_successors =
        base_cfg[base_cfg.entry_map[block_tail]].out;
      for(const auto base_successor_entry : base_successors)
      {
        const auto &base_successor_node = base_cfg[base_successor_entry.first];
        this->add_edge(block_index, entry_map.at(base_successor_node.PC));
      }
    }
  }

  /// Get the graph node index for \p program_point. Use this with operator[]
  /// to get the related graph node (e.g. `cfg[cfg.get_node_index(i)]`, though
  /// in that particular case you should just use `cfg.get_node(i)`). Storing
  /// node indices saves a map lookup, so it can be worthwhile when you expect
  /// to repeatedly look up the same program point.
  node_indext get_node_index(const I &program_point) const
  {
    return entry_map.at(program_point);
  }

  /// Get the CFG graph node relating to \p program_point.
  nodet &get_node(const I &program_point)
  {
    return (*this)[get_node_index(program_point)];
  }

  /// Get the CFG graph node relating to \p program_point.
  const nodet &get_node(const I &program_point) const
  {
    return (*this)[get_node_index(program_point)];
  }

  void insert_instruction_after(const I new_instruction, const I insert_after)
  {
    const auto existing_block_index = entry_map.at(insert_after);
    auto &existing_block = (*this)[existing_block_index].block;
    const auto insert_after_iterator =
      std::find(existing_block.begin(), existing_block.end(), insert_after);
    INVARIANT(
      insert_after_iterator != existing_block.end(),
      "entry_map should be consistent with block members");
    existing_block.insert(std::next(insert_after_iterator), new_instruction);
    entry_map[new_instruction] = existing_block_index;
  }

  node_indext split_basic_block_after(const I instruction)
  {
    // Split the existing basic block in half:
    const auto existing_block_index = entry_map.at(instruction);
    auto &existing_block = (*this)[existing_block_index].block;
    const auto split_after_iterator =
      std::find(existing_block.begin(), existing_block.end(), instruction);
    INVARIANT(
      split_after_iterator != existing_block.end(),
      "entry_map should be consistent with block members");
    std::vector<I> new_block;
    new_block.insert(
      new_block.end(), split_after_iterator, existing_block.end());
    const auto new_block_index = this->add_node(std::move(new_block));

    // Move all existing block -> successor edges to the new one:
    auto existing_successors = (*this)[existing_block_index].out;
    for(const auto &successor : existing_successors)
    {
      this->remove_edge(existing_block_index, successor.first);
      this->add_edge(new_block_index, successor.first);
    }

    // Create an edge existing -> new:
    this->add_edge(existing_block_index, new_block_index);

    // Update the entry map:
    for(const auto moved_instruction : (*this)[new_block_index].block)
      entry_map[moved_instruction] = new_block_index;

    return new_block_index;
  }

  void
  add_basic_block_graph_edge(const I from_block_tail, const I to_block_head)
  {
    const auto from_block_index = entry_map.at(from_block_tail);
    const auto to_block_index = entry_map.at(to_block_head);
    INVARIANT(
      (*this)[from_block_index].block.back() == from_block_tail,
      "from_block_tail should be a block tail");
    INVARIANT(
      (*this)[to_block_index].block.front() == to_block_head,
      "to_block_head should be a block head");
    this->add_edge(from_block_index, to_block_index);
  }

  static I get_first_node(P &program)
  {
    return base_cfgt::get_first_node(program);
  }
  static I get_last_node(P &program)
  {
    return base_cfgt::get_last_node(program);
  }
  static bool nodes_empty(P &program)
  {
    return base_cfgt::nodes_empty(program);
  }
};

#endif // CPROVER_GOTO_PROGRAMS_CFG_H
