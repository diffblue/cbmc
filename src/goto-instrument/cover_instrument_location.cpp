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
  const irep_idt &function_id,
  goto_programt &goto_program,
  goto_programt::targett &i_it,
  const cover_blocks_baset &basic_blocks,
  const assertion_factoryt &make_assertion) const
{
  if(is_non_cover_assertion(i_it))
    i_it->turn_into_skip();

  const std::size_t block_nr = basic_blocks.block_of(i_it);
  const auto representative_instruction = basic_blocks.instruction_of(block_nr);
  // we only instrument the selected instruction
  if(representative_instruction && *representative_instruction == i_it)
  {
    const std::string b = std::to_string(block_nr + 1); // start with 1
    const std::string id = id2string(function_id) + "#" + b;
    auto source_location = basic_blocks.source_location_of(block_nr);

    // filter goals
    if(goal_filters(source_location))
    {
      const auto &source_lines = basic_blocks.source_lines_of(block_nr);
      const std::string comment =
        "block " + b + " (lines " + source_lines.to_string() + ")";
      source_location.set_basic_block_source_lines(source_lines.to_irep());
      goto_program.insert_before_swap(i_it);
      *i_it = make_assertion(false_exprt(), source_location);
      initialize_source_location(i_it, comment, function_id);
      i_it++;
    }
  }
}
