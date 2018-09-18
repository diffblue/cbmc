/*******************************************************************\

Module: Query Called Functions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Query Called Functions

#include "compute_called_functions.h"

#include <util/std_expr.h>

/// get all functions whose address is taken
void compute_address_taken_functions(
  const exprt &src,
  std::unordered_set<irep_idt> &address_taken)
{
  forall_operands(it, src)
    compute_address_taken_functions(*it, address_taken);

  if(src.id() == ID_address_of)
  {
    const address_of_exprt &address = to_address_of_expr(src);

    if(
      address.type().id() == ID_pointer &&
      address.type().subtype().id() == ID_code)
    {
      const exprt &target = address.object();
      if(target.id() == ID_symbol)
        address_taken.insert(to_symbol_expr(target).get_identifier());
    }
  }
}

/// get all functions in the expression
void compute_functions(
  const exprt &src,
  std::unordered_set<irep_idt> &address_taken)
{
  forall_operands(it, src)
    compute_functions(*it, address_taken);

  if(src.type().id()==ID_code &&
     src.id()==ID_symbol)
    address_taken.insert(to_symbol_expr(src).get_identifier());
}

/// get all functions whose address is taken
void compute_address_taken_functions(
  const goto_programt &goto_program,
  std::unordered_set<irep_idt> &address_taken)
{
  forall_goto_program_instructions(it, goto_program)
  {
    compute_address_taken_functions(it->guard, address_taken);
    compute_address_taken_functions(it->code, address_taken);
  }
}

/// get all functions whose address is taken
void compute_address_taken_functions(
  const goto_functionst &goto_functions,
  std::unordered_set<irep_idt> &address_taken)
{
  forall_goto_functions(it, goto_functions)
    compute_address_taken_functions(it->second.body, address_taken);
}

/// get all functions whose address is taken
std::unordered_set<irep_idt>
compute_address_taken_functions(const goto_functionst &goto_functions)
{
  std::unordered_set<irep_idt> address_taken;
  compute_address_taken_functions(goto_functions, address_taken);
  return address_taken;
}

/// computes the functions that are (potentially) called
std::unordered_set<irep_idt>
compute_called_functions(const goto_functionst &goto_functions)
{
  std::unordered_set<irep_idt> working_queue;
  std::unordered_set<irep_idt> functions;

  // start from entry point
  working_queue.insert(goto_functions.entry_point());

  while(!working_queue.empty())
  {
    irep_idt id=*working_queue.begin();
    working_queue.erase(working_queue.begin());

    if(!functions.insert(id).second)
      continue;

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

  return functions;
}

/// computes the functions that are (potentially) called
std::unordered_set<irep_idt>
compute_called_functions(const goto_modelt &goto_model)
{
  return compute_called_functions(goto_model.goto_functions);
}
