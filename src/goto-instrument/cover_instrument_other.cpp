/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Further coverage instrumentations

#include "cover_instrument.h"

#include <util/cprover_prefix.h>

#include <langapi/language_util.h>

#include <algorithm>

void cover_path_instrumentert::instrument(
  const irep_idt &,
  goto_programt &,
  goto_programt::targett &i_it,
  const cover_blocks_baset &,
  const assertion_factoryt &) const
{
  if(is_non_cover_assertion(i_it))
    i_it->turn_into_skip();

  // TODO: implement
}

void cover_assertion_instrumentert::instrument(
  const irep_idt &function_id,
  goto_programt &,
  goto_programt::targett &i_it,
  const cover_blocks_baset &,
  const assertion_factoryt &) const
{
  // turn into 'assert(false)' to avoid simplification
  if(is_non_cover_assertion(i_it))
  {
    i_it->condition_nonconst() = false_exprt();
    initialize_source_location(
      i_it, id2string(i_it->source_location().get_comment()), function_id);
  }
}

void cover_cover_instrumentert::instrument(
  const irep_idt &function_id,
  goto_programt &,
  goto_programt::targett &i_it,
  const cover_blocks_baset &,
  const assertion_factoryt &make_assertion) const
{
  // turn __CPROVER_cover(x) into 'assert(!x)'
  if(i_it->is_function_call())
  {
    const auto &function = i_it->call_function();
    if(
      function.id() == ID_symbol &&
      to_symbol_expr(function).get_identifier() == CPROVER_PREFIX "cover" &&
      i_it->call_arguments().size() == 1)
    {
      const exprt c = i_it->call_arguments()[0];
      *i_it = make_assertion(not_exprt(c), i_it->source_location());
      std::string comment = "condition '" + from_expr(ns, function_id, c) + "'";
      initialize_source_location(i_it, comment, function_id);
    }
  }
  else if(is_non_cover_assertion(i_it))
    i_it->turn_into_skip();
}

void cover_instrument_end_of_function(
  const irep_idt &function_id,
  goto_programt &goto_program,
  const cover_instrumenter_baset::assertion_factoryt &make_assertion)
{
  const auto last_function_call = std::find_if(
    goto_program.instructions.rbegin(),
    goto_program.instructions.rend(),
    [](const goto_programt::instructiont &instruction) {
      return instruction.is_function_call();
    });
  INVARIANT(
    last_function_call != goto_program.instructions.rend(),
    "Goto program should have at least one function call");
  INVARIANT(
    last_function_call != goto_program.instructions.rbegin(),
    "Goto program shouldn't end with a function call");
  const auto if_it = last_function_call.base();
  const auto location = if_it->source_location();
  const std::string &comment =
    "additional goal to ensure reachability of end of function";
  goto_program.insert_before_swap(if_it);
  *if_it = make_assertion(false_exprt(), location);
  if_it->source_location_nonconst().set_comment(comment);
  if_it->source_location_nonconst().set_property_class(
    "reachability_constraint");
  if_it->source_location_nonconst().set_function(function_id);
}
