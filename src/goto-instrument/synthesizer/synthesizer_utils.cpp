/*******************************************************************\

Module: Utility functions for loop invariant synthesizer.

Author: Qinheping Hu

\*******************************************************************/

#include "synthesizer_utils.h"

#include <analyses/natural_loops.h>
#include <goto-instrument/contracts/utils.h>
#include <goto-instrument/havoc_utils.h>

#include <climits>
#include <sstream>

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
    unsigned int loop_number = loop_id.loop_number.value();

    // get the last instruction of the target loop
    auto &function = goto_model.goto_functions.function_map[function_id];
    goto_programt::targett loop_end = get_loop_end(loop_number, function);

    // annotate the invariant to the condition of `loop_end`
    loop_end->condition_nonconst().add(ID_C_spec_loop_invariant) =
      invariant_map_entry.second;
  }
}

bool is_instruction_in_transfomed_loop(
  const loop_idt &loop_id,
  const goto_functiont &function,
  unsigned location_number_of_target)
{
  // The loop body after transformation are instructions from
  // loop havocing instructions
  // to
  // loop end of transformed code.

  bool result = false;
  unsigned location_number_of_havocing = UINT_MAX;
  for(goto_programt::const_targett it = function.body.instructions.begin();
      it != function.body.instructions.end();
      ++it)
  {
    if(is_loop_havoc(*it) && it->loop_number == loop_id.loop_number.value())
    {
      location_number_of_havocing = it->location_number;
    }

    if(
      is_transformed_loop_end(it) &&
      it->loop_number == loop_id.loop_number.value())
    {
      result =
        result || (location_number_of_havocing < location_number_of_target &&
                   location_number_of_target < it->location_number);
    }
  }

  return result;
}

std::size_t hex_to_size_t(const std::string &hex_str)
{
  std::istringstream converter(hex_str);
  size_t result;
  converter >> std::hex >> result;
  return result;
}

invariant_mapt combine_in_and_post_invariant_clauses(
  const invariant_mapt &in_clauses,
  const invariant_mapt &post_clauses,
  const invariant_mapt &neg_guards)
{
  //  Combine invariant
  //   (in_inv || !guard) && (!guard -> pos_inv)
  invariant_mapt result;
  for(const auto &in_clause : in_clauses)
  {
    const auto &id = in_clause.first;
    INVARIANT(neg_guards.count(id), "Some loop guard is missing.");

    result[id] = and_exprt(
      or_exprt(neg_guards.at(id), in_clause.second),
      implies_exprt(neg_guards.at(id), post_clauses.at(id)));
  }
  return result;
}
