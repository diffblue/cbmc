/*******************************************************************\

Module: Ensure one backedge per target

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Ensure one backedge per target

#include "ensure_one_backedge_per_target.h"

#include "goto_model.h"

#include <algorithm>

static bool location_number_less_than(
  const goto_programt::targett &a,
  const goto_programt::targett &b)
{
  return a->location_number < b->location_number;
}

bool ensure_one_backedge_per_target(
  goto_programt::targett &it,
  goto_programt &goto_program)
{
  auto &instruction = *it;
  std::vector<goto_programt::targett> backedges;

  // Check if this instruction has multiple incoming edges from (lexically)
  // lower down the program. These aren't necessarily loop backedges (in fact
  // the program might be acyclic), but that's the most common case.
  for(auto predecessor : instruction.incoming_edges)
  {
    if(predecessor->location_number > instruction.location_number)
      backedges.push_back(predecessor);
  }

  if(backedges.size() < 2)
    return false;

  std::sort(backedges.begin(), backedges.end(), location_number_less_than);

  auto last_backedge = backedges.back();
  backedges.pop_back();

  // Can't transform if the bottom of the (probably) loop is of unexpected
  // form:
  if(!last_backedge->is_goto() || last_backedge->targets.size() > 1)
  {
    return false;
  }

  // If the last backedge is a conditional jump, add an extra unconditional
  // backedge after it:
  if(!last_backedge->condition().is_true())
  {
    auto new_goto =
      goto_program.insert_after(last_backedge, goto_programt::make_goto(it));
    // Turn the existing `if(x) goto head; succ: ...`
    // into `if(!x) goto succ; goto head; succ: ...`
    last_backedge->condition_nonconst() = not_exprt(last_backedge->condition());
    last_backedge->set_target(std::next(new_goto));
    // Use the new backedge as the one true way to the header:
    last_backedge = new_goto;
  }

  // Redirect all but one of the backedges to the last one.
  // For example, transform
  // "a: if(x) goto a; if(y) goto a;" into
  // "a: if(x) goto b; if(y) b: goto a;"
  // In the common case where this is a natural loop this corresponds to
  // branching to the bottom of the loop on a `continue` statement.
  for(auto backedge : backedges)
  {
    if(backedge->is_goto() && backedge->targets.size() == 1)
    {
      backedge->set_target(last_backedge);
    }
  }

  return true;
}

bool ensure_one_backedge_per_target(goto_programt &goto_program)
{
  bool any_change = false;

  for(auto it = goto_program.instructions.begin();
      it != goto_program.instructions.end();
      ++it)
  {
    any_change |= ensure_one_backedge_per_target(it, goto_program);
  }

  return any_change;
}

bool ensure_one_backedge_per_target(goto_model_functiont &goto_model_function)
{
  auto &goto_function = goto_model_function.get_goto_function();

  if(ensure_one_backedge_per_target(goto_function.body))
  {
    goto_function.body.update();
    goto_model_function.compute_location_numbers();
    return true;
  }

  return false;
}

bool ensure_one_backedge_per_target(goto_modelt &goto_model)
{
  bool any_change = false;

  for(auto &id_and_function : goto_model.goto_functions.function_map)
    any_change |= ensure_one_backedge_per_target(id_and_function.second.body);

  if(any_change)
    goto_model.goto_functions.update();

  return any_change;
}
