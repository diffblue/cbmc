/*******************************************************************\

Module: Synthesize Loop Invariants

Author: Qinheping Hu

\*******************************************************************/

/// \file
/// Synthesize Loop Invariants

#include "loop_invariant_synthesizer.h"

void enumerative_loop_invariant_synthesizert::init_candidates()
{
  for(auto &function_p : goto_model.goto_functions.function_map)
  {
    natural_loops_mutablet natural_loops(function_p.second.body);

    // Initialize invairants for unannotated loops as true
    for(unsigned int idx = 0; idx < natural_loops.loop_map.size(); idx++)
    {
      loop_idt new_id;
      new_id.func_name = function_p.first;
      new_id.loop_number = idx;

      // find the `loop_number`th loop
      goto_programt::targett loop_end = get_loop_end(idx, function_p.second);

      // we only synthesize invariants for unannotated loops
      if(loop_end->condition().find(ID_C_spec_loop_invariant).is_nil())
      {
        invariant_candiate_map[new_id] = true_exprt();
      }
    }
  }
}

invariant_mapt enumerative_loop_invariant_synthesizert::synthesize()
{
  init_candidates();

  // Now this method only generate true for all unnotated loops.
  // The implementation will be added later.
  return invariant_candiate_map;
}
