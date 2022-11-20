/*******************************************************************\

Module: Enumerative Loop Invariant Synthesizer

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Enumerative Loop Invariant Synthesizer

#include "enumerative_loop_invariant_synthesizer.h"

#include <analyses/natural_loops.h>

void enumerative_loop_invariant_synthesizert::init_candidates()
{
  for(auto &function_p : goto_model.goto_functions.function_map)
  {
    natural_loopst natural_loops;
    natural_loops(function_p.second.body);

    // Initialize invariants for unannotated loops as true
    for(const auto &loop_head_and_content : natural_loops.loop_map)
    {
      goto_programt::const_targett loop_end =
        get_loop_end_from_loop_head_and_content(
          loop_head_and_content.first, loop_head_and_content.second);

      loop_idt new_id(function_p.first, loop_end->loop_number);

      // we only synthesize invariants for unannotated loops
      if(loop_end->condition().find(ID_C_spec_loop_invariant).is_nil())
      {
        invariant_candiate_map[new_id] = true_exprt();
      }
    }
  }
}

invariant_mapt enumerative_loop_invariant_synthesizert::synthesize_all()
{
  init_candidates();

  // Now this method only generate true for all unnotated loops.
  // The implementation will be added later.
  return invariant_candiate_map;
}

exprt enumerative_loop_invariant_synthesizert::synthesize(loop_idt loop_id)
{
  return true_exprt();
}
