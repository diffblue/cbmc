/*******************************************************************\

Module: Query Called Functions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>

#include "compute_called_functions.h"

/*******************************************************************\

Function: compute_address_taken_functions

  Inputs:

 Outputs:

 Purpose: get all functions whose address is taken

\*******************************************************************/

void compute_address_taken_functions(
  const exprt &src,
  std::set<irep_idt> &address_taken)
{
  forall_operands(it, src)
    compute_address_taken_functions(*it, address_taken);
    
  if(src.id()==ID_address_of &&
     src.type().id()==ID_pointer &&
     src.type().subtype().id()==ID_code)
  {
    assert(src.operands().size()==1);
    const exprt &op=src.op0();
    if(op.id()==ID_symbol)
      address_taken.insert(to_symbol_expr(op).get_identifier());
  }
}

/*******************************************************************\

Function: compute_functions

  Inputs:

 Outputs:

 Purpose: get all functions in the expression

\*******************************************************************/

void compute_functions(
  const exprt &src,
  std::set<irep_idt> &address_taken)
{
  forall_operands(it, src)
    compute_functions(*it, address_taken);
    
  if(src.type().id()==ID_code &&
     src.id()==ID_symbol)
    address_taken.insert(to_symbol_expr(src).get_identifier());
}

/*******************************************************************\

Function: compute_address_taken_functions

  Inputs:

 Outputs:

 Purpose: get all functions whose address is taken

\*******************************************************************/

void compute_address_taken_functions(
  const goto_programt &goto_program,
  std::set<irep_idt> &address_taken)
{
  forall_goto_program_instructions(it, goto_program)
  {
    compute_address_taken_functions(it->guard, address_taken);
    compute_address_taken_functions(it->code, address_taken);
  }
}

/*******************************************************************\

Function: compute_address_taken_functions

  Inputs:

 Outputs:

 Purpose: get all functions whose address is taken

\*******************************************************************/

void compute_address_taken_functions(
  const goto_functionst &goto_functions,
  std::set<irep_idt> &address_taken)
{
  forall_goto_functions(it, goto_functions)
    compute_address_taken_functions(it->second.body, address_taken);
}

/*******************************************************************\

Function: compute_called_functions

  Inputs:

 Outputs:

 Purpose: computes the functions that are (potentially) called

\*******************************************************************/

void compute_called_functions(
  const goto_functionst &goto_functions,
  std::set<irep_idt> &functions)
{
  std::set<irep_idt> working_queue;
  std::set<irep_idt> done;
  
  // start from entry point
  working_queue.insert(goto_functions.main_id());
  
  while(!working_queue.empty())
  {
    irep_idt id=*working_queue.begin();
    working_queue.erase(working_queue.begin());
    
    if(done.find(id)!=done.end())
      continue;
      
    functions.insert(id);
    done.insert(id);
    
    const goto_functionst::function_mapt::const_iterator f_it=
      goto_functions.function_map.find(id);
      
    if(f_it==goto_functions.function_map.end())
      continue;
    
    const goto_programt &program=
      f_it->second.body;
      
    compute_address_taken_functions(program, working_queue);

    forall_goto_program_instructions(i_it, program)
    {
      if(i_it->is_function_call())
      {
        compute_functions(
          to_code_function_call(i_it->code).function(),
          working_queue);
      }
    }
  }
  
}
