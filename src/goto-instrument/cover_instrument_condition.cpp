/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Coverage Instrumentation for Conditions

#include "cover_instrument.h"

#include <langapi/language_util.h>

#include "cover_util.h"

void cover_condition_instrumentert::instrument(
  const irep_idt &function_id,
  goto_programt &goto_program,
  goto_programt::targett &i_it,
  const cover_blocks_baset &,
  const assertion_factoryt &make_assertion) const
{
  if(is_non_cover_assertion(i_it))
    i_it->turn_into_skip();

  // Conditions are all atomic predicates in the programs.
  if(!i_it->source_location().is_built_in())
  {
    const std::set<exprt> conditions = collect_conditions(i_it);

    source_locationt source_location = i_it->source_location();

    for(const auto &c : conditions)
    {
      const std::string c_string = from_expr(ns, function_id, c);

      const std::string comment_t = "condition '" + c_string + "' true";
      goto_program.insert_before_swap(i_it);
      initialize_source_location(source_location, comment_t, function_id);
      *i_it = make_assertion(c, source_location);

      const std::string comment_f = "condition '" + c_string + "' false";
      goto_program.insert_before_swap(i_it);
      initialize_source_location(source_location, comment_f, function_id);
      *i_it = make_assertion(not_exprt(c), source_location);
    }

    for(std::size_t i = 0; i < conditions.size() * 2; i++)
      i_it++;
  }
}
