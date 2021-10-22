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
  std::size_t operator()(T &&t) const
  {
    return std::forward<T>(identity_functort{}(t));
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

    // NOLINTNEXTLINE(readability/identifiers)
    typedef typename data_typet::iterator iterator;
    // NOLINTNEXTLINE(readability/identifiers)
    typedef typename data_typet::const_iterator const_iterator;

    template <typename U>
    const_iterator find(U &&u) const { return data.find(std::forward<U>(u)); }

    iterator begin() { return data.begin(); }
    const_iterator begin() const { return data.begin(); }
    const_iterator cbegin() const { return data.cbegin(); }

    iterator end() { return data.end(); }
    const_iterator end() const { return data.end(); }
    const_iterator cend() const { return data.cend(); }

    explicit entry_mapt(grapht< cfg_base_nodet<T, I> > &_container):
      container(_container)
    {
    }

    entryt &operator[](const goto_programt::const_targett &t)
    {
      auto e=data.insert(std::make_pair(t, 0));

      if(e.second)
        e.first->second=container.add_node();

      return e.first->second;
    }

    entryt &at(const goto_programt::const_targett &t)
    {
      return data.at(t);
    }
    const entryt &at(const goto_programt::const_targett &t) const
    {
      return data.at(t);
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
      possible_keys.reserve(possible_keys.size() + instructions.size());
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
    possible_keys.reserve(instructions.size());
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

  /// Get a map from program points to their corresponding node indices. Use
  /// the indices with `operator[]` similar to those returned by
  /// \ref get_node_index.
  const entry_mapt &entries() const
  {
    return entry_map;
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
  const exprt &function = instruction.call_function();

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
  const exprt &function = instruction.call_function();

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
  switch(instruction.type())
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
  case SET_RETURN_VALUE:
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
  for(const auto &gf_entry : goto_functions.function_map)
  {
    if(gf_entry.second.body_available())
      compute_edges(goto_functions, gf_entry.second.body);
  }
}

#endif // CPROVER_GOTO_PROGRAMS_CFG_H
