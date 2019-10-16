/*******************************************************************\

Module: Symbolic Execution

Author: John Dumbell

\*******************************************************************/

#include "complexity_limiter.h"
#include "goto_symex_state.h"
#include <cmath>

complexity_limitert::complexity_limitert(
  message_handlert &message_handler,
  const optionst &options)
  : log(message_handler)
{
  std::size_t limit = options.get_signed_int_option("symex-complexity-limit");
  if((complexity_active = limit > 0))
  {
    // This gives a curve that allows low limits to be rightly restrictive,
    // while larger numbers are very large.
    max_complexity = static_cast<std::size_t>((limit * limit) * 25);

    const std::size_t failed_child_loops_limit = options.get_signed_int_option(
      "symex-complexity-failed-child-loops-limit");
    const std::size_t unwind = options.get_signed_int_option("unwind");

    // If we have complexity enabled, try to work out a failed_children_limit.
    // In order of priority:
    //  * explicit limit
    //  * inferred limit from unwind
    //  * best limit we can apply with very little information.
    if(failed_child_loops_limit > 0)
      max_loops_complexity = failed_child_loops_limit;
    else if(unwind > 0)
      max_loops_complexity = std::max(static_cast<int>(floor(unwind / 3)), 1);
    else
      max_loops_complexity = limit;
  }
}

framet::active_loop_infot *
complexity_limitert::get_current_active_loop(call_stackt &current_call_stack)
{
  for(auto frame_iter = current_call_stack.rbegin();
      frame_iter != current_call_stack.rend();
      ++frame_iter)
  {
    // As we're walking bottom-up, the first frame we find with active loops
    // is our closest active one.
    if(!frame_iter->active_loops.empty())
    {
      return &frame_iter->active_loops.back();
    }
  }

  return {};
}

bool complexity_limitert::in_blacklisted_loop(
  const call_stackt &current_call_stack,
  const goto_programt::const_targett &instr)
{
  for(auto frame_iter = current_call_stack.rbegin();
      frame_iter != current_call_stack.rend();
      ++frame_iter)
  {
    for(auto &loop_iter : frame_iter->active_loops)
    {
      for(auto &blacklisted_loop : loop_iter.blacklisted_loops)
      {
        if(blacklisted_loop.get().contains(instr))
        {
          return true;
        }
      }
    }
  }

  return false;
}

bool complexity_limitert::are_loop_children_too_complicated(
  call_stackt &current_call_stack)
{
  std::size_t sum_complexity = 0;

  // This will walk all currently active loops, from inner-most to outer-most,
  // and sum the times their branches have failed.
  //
  // If we find that this sum is higher than our max_loops_complexity we take
  // note of the loop that happens in and then cause every parent still
  // executing that loop to blacklist it.
  //
  // This acts as a context-sensitive loop cancel, so if we've got unwind 20
  // and find out at the 3rd iteration a particular nested loop is too
  // complicated, we make sure we don't execute it the other 17 times. But as
  // soon as we're running the loop again via a different context it gets a
  // chance to redeem itself.
  optionalt<std::reference_wrapper<lexical_loopst::loopt>> loop_to_blacklist;
  for(auto frame_iter = current_call_stack.rbegin();
      frame_iter != current_call_stack.rend();
      ++frame_iter)
  {
    for(auto it = frame_iter->active_loops.rbegin();
        it != frame_iter->active_loops.rend();
        it++)
    {
      auto &loop_info = *it;

      // Because we're walking in reverse this will only be non-empty for
      // parents of the loop that's been blacklisted. We then add that to their
      // internal lists of blacklisted children.
      if(loop_to_blacklist)
      {
        loop_info.blacklisted_loops.emplace_back(*loop_to_blacklist);
      }
      else
      {
        sum_complexity += loop_info.children_too_complex;
        if(sum_complexity > max_loops_complexity)
        {
          loop_to_blacklist =
            std::reference_wrapper<lexical_loopst::loopt>(loop_info.loop);
        }
      }
    }
  }

  return !loop_to_blacklist;
}

complexity_violationt
complexity_limitert::check_complexity(goto_symex_statet &state)
{
  if(!complexity_limits_active() || !state.reachable)
    return complexity_violationt::NONE;

  std::size_t complexity = state.complexity();
  if(complexity == 0)
    return complexity_violationt::NONE;

  auto &current_call_stack = state.call_stack();

  // Check if this branch is too complicated to continue.
  auto active_loop = get_current_active_loop(current_call_stack);
  if(complexity >= max_complexity)
  {
    // If we're too complex, add a counter to the current loop we're in and
    // check if we've violated child-loop complexity limits.
    if(active_loop != nullptr)
    {
      active_loop->children_too_complex++;

      // If we're considered too complex, cancel branch.
      if(are_loop_children_too_complicated(current_call_stack))
      {
        log.warning()
          << "[symex-complexity] Loop operations considered too complex"
          << (state.source.pc->source_location.is_not_nil()
                ? " at: " + state.source.pc->source_location.as_string()
                : ", location number: " +
                    std::to_string(state.source.pc->location_number) + ".")
          << messaget::eom;

        return complexity_violationt::LOOP;
      }
    }

    log.warning() << "[symex-complexity] Branch considered too complex"
                  << (state.source.pc->source_location.is_not_nil()
                        ? " at: " + state.source.pc->source_location.as_string()
                        : ", location number: " +
                            std::to_string(state.source.pc->location_number) +
                            ".")
                  << messaget::eom;

    // Then kill this branch.
    return complexity_violationt::BRANCH;
  }

  // If we're not in any loop, return with no violation.
  if(!active_loop)
    return complexity_violationt::NONE;

  // Check if we've entered a loop that has been previously black-listed, and
  // if so then cancel before we go any further.
  if(in_blacklisted_loop(current_call_stack, state.source.pc))
  {
    log.warning() << "[symex-complexity] Trying to enter blacklisted loop"
                  << (state.source.pc->source_location.is_not_nil()
                        ? " at: " + state.source.pc->source_location.as_string()
                        : ", location number: " +
                            std::to_string(state.source.pc->location_number) +
                            ".")
                  << messaget::eom;

    return complexity_violationt::LOOP;
  }

  return complexity_violationt::NONE;
}

void complexity_limitert::run_transformations(
  complexity_violationt complexity_violation,
  goto_symex_statet &current_state)
{
  if(violation_transformations.empty())
    default_transformation.transform(complexity_violation, current_state);
  else
    for(auto transform_lambda : violation_transformations)
      transform_lambda.transform(complexity_violation, current_state);
}
