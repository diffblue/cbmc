/*******************************************************************\

Module: Ensure one backedge per target

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Ensure one backedge per target

#include "ensure_one_backedge_per_target.h"

#include <analyses/natural_loops.h>

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

struct instruction_location_numbert : public goto_programt::targett
{
  // Implicit conversion from a goto_programt::targett is permitted.
  // NOLINTNEXTLINE(runtime/explicit)
  instruction_location_numbert(goto_programt::targett target)
    : goto_programt::targett(target)
  {
  }

  instruction_location_numbert() = default;
};

inline bool operator<(
  const instruction_location_numbert &i1,
  const instruction_location_numbert &i2)
{
  return i1->location_number < i2->location_number;
}

bool ensure_one_backedge_per_target(goto_programt &goto_program)
{
  natural_loops_templatet<goto_programt, instruction_location_numbert>
    natural_loops{goto_program};
  std::set<instruction_location_numbert> modified_loops;

  for(auto it1 = natural_loops.loop_map.begin();
      it1 != natural_loops.loop_map.end();
      ++it1)
  {
    DATA_INVARIANT(!it1->second.empty(), "loops cannot have no instructions");
    // skip over lexical loops
    if(
      (*std::prev(it1->second.end()))->is_goto() &&
      (*std::prev(it1->second.end()))->get_target() == it1->first)
      continue;
    if(modified_loops.find(it1->first) != modified_loops.end())
      continue;
    // it1 refers to a loop that isn't a lexical loop, now see whether any other
    // loop is nested within it1
    for(auto it2 = natural_loops.loop_map.begin();
        it2 != natural_loops.loop_map.end();
        ++it2)
    {
      if(it1 == it2)
        continue;

      if(std::includes(
           it1->second.begin(),
           it1->second.end(),
           it2->second.begin(),
           it2->second.end()))
      {
        // make sure that loops with overlapping body are properly nested by a
        // back edge; this will be a disconnected edge, which
        // ensure_one_backedge_per_target connects
        if(
          modified_loops.find(it2->first) == modified_loops.end() &&
          (!(*std::prev(it2->second.end()))->is_goto() ||
           (*std::prev(it2->second.end()))->get_target() != it2->first))
        {
          auto new_goto = goto_program.insert_after(
            *std::prev(it2->second.end()),
            goto_programt::make_goto(
              it2->first, (*std::prev(it2->second.end()))->source_location()));
          it2->second.insert_instruction(new_goto);
          it1->second.insert_instruction(new_goto);
          modified_loops.insert(it2->first);
        }

        goto_program.insert_after(
          *std::prev(it1->second.end()),
          goto_programt::make_goto(
            it1->first, (*std::prev(it1->second.end()))->source_location()));
        modified_loops.insert(it1->first);
        break;
      }
    }
  }

  if(!modified_loops.empty())
    goto_program.update();

  bool any_change = !modified_loops.empty();

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
