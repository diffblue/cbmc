/*******************************************************************\

Module: Query Called Functions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Query Called Functions

#include "compute_called_functions.h"

#include <util/pointer_expr.h>
#include <util/std_expr.h>

#include "goto_model.h"

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
      to_pointer_type(address.type()).base_type().id() == ID_code)
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
  for(const auto &i : goto_program.instructions)
  {
    i.apply([&address_taken](const exprt &expr) {
      compute_address_taken_functions(expr, address_taken);
    });
  }
}

/// get all functions whose address is taken
void compute_address_taken_functions(
  const goto_functionst &goto_functions,
  std::unordered_set<irep_idt> &address_taken)
{
  for(const auto &gf_entry : goto_functions.function_map)
    compute_address_taken_functions(gf_entry.second.body, address_taken);
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

    for(const auto &instruction : program.instructions)
    {
      if(instruction.is_function_call())
      {
        compute_functions(instruction.call_function(), working_queue);
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
