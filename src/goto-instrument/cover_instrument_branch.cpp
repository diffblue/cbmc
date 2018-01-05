/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Coverage Instrumentation for Branches

#include "cover_instrument.h"
#include "cover_basic_blocks.h"

void cover_branch_instrumentert::instrument(
  goto_programt &goto_program,
  goto_programt::targett &i_it,
  const cover_basic_blockst &basic_blocks) const
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
    initialize_source_location(t, comment, i_it->function);
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
    const irep_idt function = i_it->function;
    source_locationt source_location = i_it->source_location;

    goto_program.insert_before_swap(i_it);
    i_it->make_assertion(not_exprt(guard));
    i_it->source_location = source_location;
    initialize_source_location(i_it, true_comment, function);

    goto_program.insert_before_swap(i_it);
    i_it->make_assertion(guard);
    i_it->source_location = source_location;
    initialize_source_location(i_it, false_comment, function);

    std::advance(i_it, 2);
  }
}
