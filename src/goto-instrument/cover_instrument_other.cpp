/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Further coverage instrumentations

#include "cover_instrument.h"

#include <langapi/language_util.h>

#include "cover_util.h"

void cover_path_instrumentert::instrument(
  const irep_idt &,
  goto_programt &,
  goto_programt::targett &i_it,
  const cover_blocks_baset &) const
{
  if(is_non_cover_assertion(i_it))
    i_it->make_skip();

  // TODO: implement
}

void cover_assertion_instrumentert::instrument(
  const irep_idt &function_id,
  goto_programt &,
  goto_programt::targett &i_it,
  const cover_blocks_baset &) const
{
  // turn into 'assert(false)' to avoid simplification
  if(is_non_cover_assertion(i_it))
  {
    i_it->guard = false_exprt();
    initialize_source_location(
      i_it, id2string(i_it->source_location.get_comment()), function_id);
  }
}

void cover_cover_instrumentert::instrument(
  const irep_idt &function_id,
  goto_programt &,
  goto_programt::targett &i_it,
  const cover_blocks_baset &) const
{
  // turn __CPROVER_cover(x) into 'assert(!x)'
  if(i_it->is_function_call())
  {
    const code_function_callt &code_function_call =
      to_code_function_call(i_it->code);
    if(
      code_function_call.function().id() == ID_symbol &&
      to_symbol_expr(code_function_call.function()).get_identifier() ==
        CPROVER_PREFIX "cover" &&
      code_function_call.arguments().size() == 1)
    {
      const exprt c = code_function_call.arguments()[0];
      std::string comment = "condition `" + from_expr(ns, function_id, c) + "'";
      i_it->guard = not_exprt(c);
      i_it->type = ASSERT;
      i_it->code.clear();
      initialize_source_location(i_it, comment, function_id);
    }
  }
  else if(is_non_cover_assertion(i_it))
    i_it->make_skip();
}

void cover_instrument_end_of_function(
  const irep_idt &function_id,
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
  if_it->source_location.set_function(function_id);
  if_it->function = function_id;
}
