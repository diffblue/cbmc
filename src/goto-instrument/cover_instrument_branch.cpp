/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Coverage Instrumentation for Branches

#include "cover_instrument.h"
#include "cover_basic_blocks.h"

void cover_branch_instrumentert::instrument(
  const irep_idt &function_id,
  goto_programt &goto_program,
  goto_programt::targett &i_it,
  const cover_blocks_baset &basic_blocks) const
{
  if(is_non_cover_assertion(i_it))
    i_it->make_skip();

  if(i_it == goto_program.instructions.begin())
  {
    // we want branch coverage to imply 'entry point of function'
    // coverage
    std::string comment = "entry point";

    source_locationt source_location = i_it->source_location;

    goto_programt::targett t = goto_program.insert_before(i_it);
    t->make_assertion(false_exprt());
    t->source_location = source_location;
    initialize_source_location(t, comment, function_id);
  }

  if(
    i_it->is_goto() && !i_it->guard.is_true() &&
    !i_it->source_location.is_built_in())
  {
    std::string b =
      std::to_string(basic_blocks.block_of(i_it) + 1); // start with 1
    std::string true_comment = "block " + b + " branch true";
    std::string false_comment = "block " + b + " branch false";

    exprt guard = i_it->guard;
    source_locationt source_location = i_it->source_location;

    goto_program.insert_before_swap(i_it);
    i_it->make_assertion(not_exprt(guard));
    i_it->source_location = source_location;
    initialize_source_location(i_it, true_comment, function_id);

    goto_program.insert_before_swap(i_it);
    i_it->make_assertion(guard);
    i_it->source_location = source_location;
    initialize_source_location(i_it, false_comment, function_id);

    std::advance(i_it, 2);
  }
}
