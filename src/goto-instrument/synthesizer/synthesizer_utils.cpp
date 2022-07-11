/*******************************************************************\

Module: Utility functions for loop invariant synthesizer.

Author: Qinheping Hu

\*******************************************************************/

#include "synthesizer_utils.h"

goto_programt::targett get_loop_head_or_end(
  const unsigned int target_loop_number,
  goto_functiont &function,
  bool finding_head)
{
  natural_loops_mutablet natural_loops(function.body);

  // iterate over all natural loops to find the loop with `target_loop_number`
  for(const auto &loop_p : natural_loops.loop_map)
  {
    const goto_programt::targett loop_head = loop_p.first;
    goto_programt::targett loop_end = loop_p.first;
    const loopt &loop = loop_p.second;
    for(const auto &t : loop)
    {
      // an instruction is the loop end if it is a goto instruction
      // and it jumps backward to the loop head
      if(
        t->is_goto() && t->get_target() == loop_head &&
        t->location_number > loop_end->location_number)
        loop_end = t;
    }

    // check if the current loop is the target loop by comparing loop number
    if(loop_end->loop_number == target_loop_number)
    {
      if(finding_head)
        return loop_head;
      else
        return loop_end;
    }
  }

  UNREACHABLE;
}

goto_programt::targett
get_loop_end(const unsigned int target_loop_number, goto_functiont &function)
{
  return get_loop_head_or_end(target_loop_number, function, false);
}

goto_programt::targett
get_loop_head(const unsigned int target_loop_number, goto_functiont &function)
{
  return get_loop_head_or_end(target_loop_number, function, true);
}

void annotate_invariants(
  const invariant_mapt &invariant_map,
  goto_modelt &goto_model,
  messaget &log)
{
  for(const auto &invariant_map_entry : invariant_map)
  {
    loop_idt loop_id = invariant_map_entry.first;
    irep_idt func_name = loop_id.func_name;
    unsigned int loop_number = loop_id.loop_number;

    // get the last instruction of the target loop
    auto &function = goto_model.goto_functions.function_map[func_name];
    goto_programt::targett loop_end = get_loop_end(loop_number, function);

    // annotate the invariant to the condition of `loop_end`
    exprt condition = loop_end->condition();
    loop_end->condition_nonconst().add(ID_C_spec_loop_invariant) =
      invariant_map_entry.second;
  }
}
