/*******************************************************************\

Module: Utility functions for loop invariant synthesizer.

Author: Qinheping Hu

\*******************************************************************/

#include "synthesizer_utils.h"

#include <util/optional.h>

#include <analyses/natural_loops.h>
#include <goto-instrument/contracts/utils.h>
#include <goto-instrument/havoc_utils.h>

goto_programt::const_targett get_loop_end_from_loop_head_and_content(
  const goto_programt::const_targett &loop_head,
  const loop_templatet<goto_programt::const_targett> &loop)
{
  goto_programt::const_targett loop_end = loop_head;
  for(const auto &t : loop)
  {
    // an instruction is the loop end if it is a goto instruction
    // and it jumps backward to the loop head
    if(
      t->is_goto() && t->get_target() == loop_head &&
      t->location_number > loop_end->location_number)
      loop_end = t;
  }
  INVARIANT(
    loop_head != loop_end,
    "Could not find end of the loop starting at: " +
      loop_head->source_location().as_string());

  return loop_end;
}

goto_programt::targett get_loop_end_from_loop_head_and_content_mutable(
  const goto_programt::targett &loop_head,
  const loop_templatet<goto_programt::targett> &loop)
{
  goto_programt::targett loop_end = loop_head;
  for(const auto &t : loop)
  {
    // an instruction is the loop end if it is a goto instruction
    // and it jumps backward to the loop head
    if(
      t->is_goto() && t->get_target() == loop_head &&
      t->location_number > loop_end->location_number)
      loop_end = t;
  }
  INVARIANT(
    loop_head != loop_end,
    "Could not find end of the loop starting at: " +
      loop_head->source_location().as_string());

  return loop_end;
}

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
    goto_programt::targett loop_end =
      get_loop_end_from_loop_head_and_content_mutable(loop_head, loop_p.second);
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
  goto_modelt &goto_model)
{
  for(const auto &invariant_map_entry : invariant_map)
  {
    loop_idt loop_id = invariant_map_entry.first;
    irep_idt function_id = loop_id.function_id;
    unsigned int loop_number = loop_id.loop_number;

    // get the last instruction of the target loop
    auto &function = goto_model.goto_functions.function_map[function_id];
    goto_programt::targett loop_end = get_loop_end(loop_number, function);

    // annotate the invariant to the condition of `loop_end`
    loop_end->condition_nonconst().add(ID_C_spec_loop_invariant) =
      invariant_map_entry.second;
  }
}

void annotate_assigns(
  const std::map<loop_idt, std::set<exprt>> &assigns_map,
  goto_modelt &goto_model)
{
  for(const auto &assigns_map_entry : assigns_map)
  {
    loop_idt loop_id = assigns_map_entry.first;
    irep_idt function_id = loop_id.function_id;
    unsigned int loop_number = loop_id.loop_number;

    // get the last instruction of the target loop
    auto &function = goto_model.goto_functions.function_map[function_id];
    goto_programt::targett loop_end = get_loop_end(loop_number, function);

    exprt &condition = loop_end->condition_nonconst();
    auto assigns = exprt(ID_target_list);
    for(const auto &e : assigns_map_entry.second)
      assigns.add_to_operands(e);
    condition.add(ID_C_spec_assigns) = assigns;
  }
}

invariant_mapt combine_in_and_post_invariant_clauses(
  const invariant_mapt &in_clauses,
  const invariant_mapt &post_clauses,
  const invariant_mapt &neg_guards)
{
  // Combine invariant
  // (in_inv || !guard) && (!guard -> pos_inv) for loops with loop guard
  // in_inv && pos_inv for loops without loop guard
  invariant_mapt result;
  for(const auto &in_clause : in_clauses)
  {
    const auto &id = in_clause.first;
    const auto &it_guard = neg_guards.find(id);

    // Unconditional loop or failed to get loop guard.
    if(it_guard == neg_guards.end())
    {
      result[id] = and_exprt(in_clause.second, post_clauses.at(id));
    }
    // Loops with loop guard.
    else
    {
      result[id] = and_exprt(
        or_exprt(it_guard->second, in_clause.second),
        implies_exprt(it_guard->second, post_clauses.at(id)));
    }
  }
  return result;
}
