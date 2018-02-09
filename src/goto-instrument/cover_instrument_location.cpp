/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Coverage Instrumentation for Location, i.e. Basic Blocks

#include "cover_instrument.h"

#include "cover_basic_blocks.h"
#include "cover_filter.h"

void cover_location_instrumentert::instrument(
  goto_programt &goto_program,
  goto_programt::targett &i_it,
  const cover_basic_blockst &basic_blocks) const
{
  if(is_non_cover_assertion(i_it))
    i_it->make_skip();

  const unsigned block_nr = basic_blocks.block_of(i_it);
  const auto representative_instruction = basic_blocks.instruction_of(block_nr);
  // we only instrument the selected instruction
  if(representative_instruction && *representative_instruction == i_it)
  {
    const std::string b = std::to_string(block_nr + 1); // start with 1
    const std::string id = id2string(i_it->function) + "#" + b;
    const auto source_location = basic_blocks.source_location_of(block_nr);

    // filter goals
    if(goal_filters(source_location))
    {
      const std::string comment = "block " + b;
      const irep_idt function = i_it->function;
      goto_program.insert_before_swap(i_it);
      i_it->make_assertion(false_exprt());
      i_it->source_location = source_location;
      initialize_source_location(i_it, comment, function);
      i_it++;
    }
  }
}
