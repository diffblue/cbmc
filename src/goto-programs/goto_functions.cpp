/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

/// \file
/// Goto Programs with Functions

#include "goto_functions.h"

void goto_functionst::output(
  const namespacet &ns,
  std::ostream &out) const
{
  for(const auto &fun : function_map)
  {
    if(fun.second.body_available())
    {
      out << "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n\n";

      const symbolt &symbol=ns.lookup(fun.first);
      out << symbol.display_name() << " /* " << symbol.name << " */\n";
      fun.second.body.output(ns, symbol.name, out);

      out << std::flush;
    }
  }
}

void goto_functionst::compute_location_numbers()
{
  unused_location_number = 0;
  for(auto &func : function_map)
  {
    // Side-effect: bumps unused_location_number.
    func.second.body.compute_location_numbers(unused_location_number);
  }
}

void goto_functionst::compute_location_numbers(
  goto_programt &program)
{
  // Renumber just this single function. Use fresh numbers in case it has
  // grown since it was last numbered.
  program.compute_location_numbers(unused_location_number);
}

void goto_functionst::compute_incoming_edges()
{
  for(auto &func : function_map)
  {
    func.second.body.compute_incoming_edges();
  }
}

void goto_functionst::compute_target_numbers()
{
  for(auto &func : function_map)
  {
    func.second.body.compute_target_numbers();
  }
}

void goto_functionst::compute_loop_numbers()
{
  for(auto &func : function_map)
  {
    func.second.body.compute_loop_numbers();
  }
}


void get_local_identifiers(
  const goto_functiont &goto_function,
  std::set<irep_idt> &dest)
{
  goto_function.body.get_decl_identifiers(dest);

  const code_typet::parameterst &parameters=
    goto_function.type.parameters();

  // add parameters
  for(const auto &param : parameters)
  {
    const irep_idt &identifier=param.get_identifier();
    if(identifier!="")
      dest.insert(identifier);
  }
}
