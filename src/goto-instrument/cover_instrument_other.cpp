/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Further coverage instrumentations

#include "cover_instrument.h"

#include "cover_util.h"

void cover_instrument_path(goto_programt::targett &i_it)
{
  if(i_it->is_assert())
    i_it->make_skip();

  // TODO: implement
}

void cover_instrument_assertion(goto_programt::targett &i_it)
{
  const irep_idt coverage_criterion = "assertion";
  const irep_idt property_class = "coverage";

  // turn into 'assert(false)' to avoid simplification
  if(i_it->is_assert())
  {
    i_it->guard = false_exprt();
    i_it->source_location.set(ID_coverage_criterion, coverage_criterion);
    i_it->source_location.set_property_class(property_class);
    i_it->source_location.set_function(i_it->function);
  }
}

void cover_instrument_cover(const namespacet &ns, goto_programt::targett &i_it)
{
  const irep_idt coverage_criterion = "cover";
  const irep_idt property_class = "coverage";

  // turn __CPROVER_cover(x) into 'assert(!x)'
  if(i_it->is_function_call())
  {
    const code_function_callt &code_function_call =
      to_code_function_call(i_it->code);
    if(
      code_function_call.function().id() == ID_symbol &&
      to_symbol_expr(code_function_call.function()).get_identifier() ==
        "__CPROVER_cover" &&
      code_function_call.arguments().size() == 1)
    {
      const exprt c = code_function_call.arguments()[0];
      std::string comment = "condition `" + from_expr(ns, "", c) + "'";
      i_it->guard = not_exprt(c);
      i_it->type = ASSERT;
      i_it->code.clear();
      i_it->source_location.set_comment(comment);
      i_it->source_location.set(ID_coverage_criterion, coverage_criterion);
      i_it->source_location.set_property_class(property_class);
      i_it->source_location.set_function(i_it->function);
    }
  }
  else if(i_it->is_assert())
    i_it->make_skip();
}

void cover_instrument_end_of_function(
  const irep_idt &function,
  goto_programt &goto_program)
{
  auto if_it = goto_program.instructions.end();
  while(!if_it->is_function_call())
    if_it--;
  if_it++;
  const std::string &comment =
    "additional goal to ensure reachability of end of function";
  goto_program.insert_before_swap(if_it);
  if_it->make_assertion(false_exprt());
  if_it->source_location.set_comment(comment);
  if_it->source_location.set_property_class("reachability_constraint");
  if_it->source_location.set_function(function);
  if_it->function = function;
}
