/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Coverage Instrumentation for Decisions

#include "cover_instrument.h"

#include "cover_util.h"

void cover_instrument_decision(
  const namespacet &ns,
  goto_programt &goto_program,
  goto_programt::targett &i_it)
{
  const irep_idt coverage_criterion = "decision";
  const irep_idt property_class = "coverage";

  if(i_it->is_assert())
    i_it->make_skip();

  // Decisions are maximal Boolean combinations of conditions.
  if(!i_it->source_location.is_built_in())
  {
    const std::set<exprt> decisions = collect_decisions(i_it);

    const source_locationt source_location = i_it->source_location;

    for(const auto &d : decisions)
    {
      const std::string d_string = from_expr(ns, "", d);

      const std::string comment_t = "decision `" + d_string + "' true";
      const irep_idt function = i_it->function;
      goto_program.insert_before_swap(i_it);
      i_it->make_assertion(d);
      i_it->source_location = source_location;
      i_it->source_location.set_comment(comment_t);
      i_it->source_location.set(ID_coverage_criterion, coverage_criterion);
      i_it->source_location.set_property_class(property_class);
      i_it->source_location.set_function(function);
      i_it->function = function;

      const std::string comment_f = "decision `" + d_string + "' false";
      goto_program.insert_before_swap(i_it);
      i_it->make_assertion(not_exprt(d));
      i_it->source_location = source_location;
      i_it->source_location.set_comment(comment_f);
      i_it->source_location.set(ID_coverage_criterion, coverage_criterion);
      i_it->source_location.set_property_class(property_class);
      i_it->source_location.set_function(function);
      i_it->function = function;
    }

    // advance iterator beyond the inserted instructions
    for(std::size_t i = 0; i < decisions.size() * 2; i++)
      i_it++;
  }
}
