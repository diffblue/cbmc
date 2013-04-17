/*******************************************************************\

Module: Printing function call sequences for Ofer

Author: Daniel Kroening

Date: April 2013

\*******************************************************************/

#include <stack>
#include <iostream>

#include <util/std_expr.h>

#include "call_sequences.h"

/*******************************************************************\

Function: show_call_sequences

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_call_sequences(
  const irep_idt &function,
  const goto_programt &goto_program,
  const goto_programt::const_targett start)
{
  std::cout << "# From " << function << std::endl;
      
  std::stack<goto_programt::const_targett> stack;
  std::set<goto_programt::const_targett> seen;
  
  if(start!=goto_program.instructions.end())
    stack.push(start);

  while(!stack.empty())
  {
    goto_programt::const_targett t=stack.top();
    stack.pop();
    
    if(!seen.insert(t).second)
      continue; // seen it already
    
    if(t->is_function_call())
    {
      const exprt &function2=to_code_function_call(t->code).function();
      if(function2.id()==ID_symbol)
      {
        // print pair function, function2
        std::cout << function << " -> "
                  << to_symbol_expr(function2).get_identifier() << std::endl;
      }
      continue; // abort search
    }

    // get successors
    goto_programt::const_targetst s;
    goto_program.get_successors(t, s);
    
    // add to stack
    for(goto_programt::const_targetst::const_iterator
        it=s.begin(); it!=s.end(); it++)
      stack.push(*it);
  }
}

/*******************************************************************\

Function: show_call_sequences

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_call_sequences(
  const irep_idt &function,
  const goto_programt &goto_program)
{
  // this is quadratic
  
  std::cout << "# " << function << std::endl;
  
  show_call_sequences(
    function,
    goto_program,
    goto_program.instructions.begin());
  
  forall_goto_program_instructions(i_it, goto_program)
  {
    if(!i_it->is_function_call())
      continue;
      
    const exprt &f1=to_code_function_call(i_it->code).function();
    
    if(f1.id()!=ID_symbol)
      continue;
      
    // find any calls reachable from this one
    goto_programt::const_targett next=i_it;
    next++;

    show_call_sequences(
      to_symbol_expr(f1).get_identifier(),
      goto_program,
      next);
  }
  
  std::cout << std::endl;
}

/*******************************************************************\

Function: show_call_sequences

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_call_sequences(const goto_functionst &goto_functions)
{
  // do per function

  forall_goto_functions(f_it, goto_functions)
    show_call_sequences(f_it->first, f_it->second.body);
}

