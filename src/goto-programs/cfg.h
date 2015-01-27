/*******************************************************************\

Module: Control Flow Graph

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_CFG_H
#define CPROVER_GOTO_PROGRAMS_CFG_H

#include <util/std_expr.h>

#include "goto_functions.h"

/*******************************************************************\

   Class: cfg_baset

 Purpose:

\*******************************************************************/

template<class T>
class cfg_baset
{
public:
  // these are the CFG nodes
  struct entryt: public T
  {
    typedef std::list<struct entryt *> entriest;

    // we have edges both ways
    entriest successors, predecessors;
    goto_programt::const_targett PC;
  };
  
  typedef entryt * iterator;
  typedef const entryt * const_iterator;

  typedef std::list<iterator> entriest;
  
  typedef std::map<goto_programt::const_targett, entryt> entry_mapt;
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

  virtual void compute_edges_return(
    const goto_programt &goto_program,
    const goto_programt::instructiont &instruction,
    goto_programt::const_targett next_PC,
    entryt &entry);

  void compute_edges(
    const goto_functionst &goto_functions,
    const goto_programt &goto_program,
    goto_programt::const_targett PC);

  void compute_edges(
    const goto_functionst &goto_functions,
    const goto_programt &goto_program);

  void compute_edges(
    const goto_functionst &goto_functions);

public:
  virtual ~cfg_baset()
  {
  }

  void operator()(
    const goto_functionst &goto_functions)
  {
    compute_edges(goto_functions);
  }

  void operator()(
    const goto_programt &goto_program)
  {
    goto_functionst goto_functions;
    compute_edges(goto_functions, goto_program);
  }

};

/*******************************************************************\

Function: cfg_baset::compute_edges_goto

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class T>
void cfg_baset<T>::compute_edges_goto(
  const goto_programt &goto_program,
  const goto_programt::instructiont &instruction,
  goto_programt::const_targett next_PC,
  entryt &entry)
{
  if(next_PC!=goto_program.instructions.end() &&
     !instruction.guard.is_true())
    entry.successors.push_back(&entry_map[next_PC]);

  for(goto_programt::instructiont::targetst::const_iterator
      t_it=instruction.targets.begin();
      t_it!=instruction.targets.end();
      t_it++)
  {
    goto_programt::const_targett t=*t_it;
    if(t!=goto_program.instructions.end())
      entry.successors.push_back(&entry_map[t]);
  }
}

/*******************************************************************\

Function: cfg_baset::compute_edges_catch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class T>
void cfg_baset<T>::compute_edges_catch(
  const goto_programt &goto_program,
  const goto_programt::instructiont &instruction,
  goto_programt::const_targett next_PC,
  entryt &entry)
{
  if(next_PC!=goto_program.instructions.end())
    entry.successors.push_back(&entry_map[next_PC]);

  // Not ideal, but preserves targets
  // Ideally, the throw statements should have those as successors

  for(goto_programt::instructiont::targetst::const_iterator
      t_it=instruction.targets.begin();
      t_it!=instruction.targets.end();
      t_it++)
  {
    goto_programt::const_targett t=*t_it;
    if(t!=goto_program.instructions.end())
      entry.successors.push_back(&entry_map[t]);
  }
}

/*******************************************************************\

Function: cfg_baset::compute_edges_throw

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class T>
void cfg_baset<T>::compute_edges_throw(
  const goto_programt &goto_program,
  const goto_programt::instructiont &instruction,
  goto_programt::const_targett next_PC,
  entryt &entry)
{
  // no (trivial) successors
}

/*******************************************************************\

Function: cfg_baset::compute_edges_start_thread

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class T>
void cfg_baset<T>::compute_edges_start_thread(
  const goto_programt &goto_program,
  const goto_programt::instructiont &instruction,
  goto_programt::const_targett next_PC,
  entryt &entry)
{
  if(next_PC!=goto_program.instructions.end())
    entry.successors.push_back(&entry_map[next_PC]);

  for(goto_programt::instructiont::targetst::const_iterator
      t_it=instruction.targets.begin();
      t_it!=instruction.targets.end();
      t_it++)
  {
    goto_programt::const_targett t=*t_it;
    if(t!=goto_program.instructions.end())
      entry.successors.push_back(&entry_map[t]);
  }
}

/*******************************************************************\

Function: cfg_baset::compute_edges_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class T>
void cfg_baset<T>::compute_edges_function_call(
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
     f_it->second.body_available)
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
      entry.successors.push_back(&entry_map[i_it]);

      // add the last instruction as predecessor of the return location
      if(next_PC!=goto_program.instructions.end())
      {
        entry_map[last_it].successors.push_back(&entry_map[next_PC]);
        entry_map[next_PC].predecessors.push_back(&entry_map[last_it]);
      }
    }
    else if(next_PC!=goto_program.instructions.end())
    {
      // empty function
      entry.successors.push_back(&entry_map[next_PC]);
    }        
  }
  else if(next_PC!=goto_program.instructions.end())
    entry.successors.push_back(&entry_map[next_PC]);
}

/*******************************************************************\

Function: cfg_baset::compute_edges_return

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class T>
void cfg_baset<T>::compute_edges_return(
  const goto_programt &goto_program,
  const goto_programt::instructiont &instruction,
  goto_programt::const_targett next_PC,
  entryt &entry)
{
  // the successor of return is the last instruction of the function,
  // normally END_FUNCTION
  if(next_PC!=goto_program.instructions.end())
    entry.successors.push_back(&entry_map[--(goto_program.instructions.end())]);
}

/*******************************************************************\

Function: cfg_baset::compute_edges

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class T>
void cfg_baset<T>::compute_edges(
  const goto_functionst &goto_functions,
  const goto_programt &goto_program,
  goto_programt::const_targett PC)
{
  const goto_programt::instructiont &instruction=*PC;
  entryt &entry=entry_map[PC];
  entry.PC=PC;
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
  case RETURN:
    compute_edges_return(goto_program, instruction, next_PC, entry);
    break;
  case ASSIGN:
  case ASSUME:
  case ASSERT:
  case OTHER:
  case SKIP:
  case END_THREAD:
  case LOCATION:
  case END_FUNCTION:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
  case DECL:
  case DEAD:
  case NO_INSTRUCTION_TYPE:
    if(next_PC!=goto_program.instructions.end())
      entry.successors.push_back(&entry_map[next_PC]);
    break;
  }

  // now do backward edges
  for(typename entriest::const_iterator
      s_it=entry.successors.begin();
      s_it!=entry.successors.end();
      s_it++)
  {
    (*s_it)->predecessors.push_back(&entry);
  }
}

/*******************************************************************\

Function: cfg_baset::compute_edges

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class T>
void cfg_baset<T>::compute_edges(
  const goto_functionst &goto_functions,
  const goto_programt &goto_program)
{
  forall_goto_program_instructions(it, goto_program)
    compute_edges(goto_functions, goto_program, it);
}

/*******************************************************************\

Function: cfg_baset::compute_edges

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class T>
void cfg_baset<T>::compute_edges(
  const goto_functionst &goto_functions)
{
  forall_goto_functions(it, goto_functions)
    if(it->second.body_available)
      compute_edges(goto_functions, it->second.body);
}

#endif
