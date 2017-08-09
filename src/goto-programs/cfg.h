/*******************************************************************\

Module: Control Flow Graph

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Control Flow Graph

#ifndef CPROVER_GOTO_PROGRAMS_CFG_H
#define CPROVER_GOTO_PROGRAMS_CFG_H

#include <util/std_expr.h>
#include <util/graph.h>

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
public:
  typedef std::size_t entryt;

  struct entry_mapt:
    public std::map<goto_programt::const_targett, entryt>
  {
    grapht< cfg_base_nodet<T, I> > &container;

    explicit entry_mapt(grapht< cfg_base_nodet<T, I> > &_container):
      container(_container)
    {
    }

    entryt &operator[](const goto_programt::const_targett &t)
    {
      std::pair<iterator, bool> e=insert(std::make_pair(t, 0));

      if(e.second)
        e.first->second=container.add_node();

      return e.first->second;
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
    compute_edges(goto_functions);
  }

  void operator()(P &goto_program)
  {
    goto_functionst goto_functions;
    compute_edges(goto_functions, goto_program);
  }

  I get_first_node(P &program) const { return program.instructions.begin(); }
  I get_last_node(P &program) const { return --program.instructions.end(); }
  bool nodes_empty(P &program) const { return program.instructions.empty(); }
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
  if(next_PC!=goto_program.instructions.end() &&
     !instruction.guard.is_true())
    this->add_edge(entry, entry_map[next_PC]);

  for(const auto &t : instruction.targets)
    if(t!=goto_program.instructions.end())
      this->add_edge(entry, entry_map[t]);
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
  const goto_programt &goto_program,
  const goto_programt::instructiont &instruction,
  goto_programt::const_targett next_PC,
  entryt &entry)
{
  // no (trivial) successors
}

template<class T, typename P, typename I>
void cfg_baset<T, P, I>::compute_edges_start_thread(
  const goto_programt &goto_program,
  const goto_programt::instructiont &instruction,
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

  for(const auto &t : instruction.targets)
    if(t!=goto_program.instructions.end())
      this->add_edge(entry, this->entry_map[t]);
}

template<class T, typename P, typename I>
void cfg_baset<T, P, I>::compute_edges_function_call(
  const goto_functionst &goto_functions,
  const goto_programt &goto_program,
  const goto_programt::instructiont &instruction,
  goto_programt::const_targett next_PC,
  entryt &entry)
{
  const exprt &function=
    to_code_function_call(instruction.code).function();

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
  const goto_functionst &goto_functions,
  const goto_programt &goto_program,
  const goto_programt::instructiont &instruction,
  goto_programt::const_targett next_PC,
  typename cfg_baset<T, P, I>::entryt &entry)
{
  const exprt &function=
    to_code_function_call(instruction.code).function();

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
    if(instruction.guard.is_false())
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
    assert(false);
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

#endif // CPROVER_GOTO_PROGRAMS_CFG_H
