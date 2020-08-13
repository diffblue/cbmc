/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Track function-local control flow for loop unwinding and path senstivity

#include "local_control_flow_history.h"

template <bool track_forward_jumps, bool track_backward_jumps>
ai_history_baset::step_returnt
local_control_flow_historyt<track_forward_jumps, track_backward_jumps>::step(
  locationt to,
  const trace_sett &others,
  trace_ptrt caller_hist) const
{
  // First compute what the new history could be,
  // then find it in others or possibly merge it if the limit is hit

  std::shared_ptr<const local_control_flow_historyt<
    track_forward_jumps,
    track_backward_jumps>>
    next_step = nullptr;

  // Local branching is the key step
  if(
    current_loc->is_goto() &&
    (current_loc->is_backwards_goto() ? track_backward_jumps
                                      : track_forward_jumps))
  {
    bool branch_taken = (current_loc->get_target() == to) &&
                        !(current_loc->get_target() == std::next(current_loc));
    // Slight oddity -- we regard branches to the next instruction as not taken
    // regardless of their guard condition.  This is slightly more general than
    // is_skip() but without changing the step() interface to have a "taken"
    // flag we will have to assume taken or not taken and not taken seems safer.

    auto decision = std::make_shared<local_control_flow_decisiont>(
      current_loc, branch_taken, control_flow_decision_history);
    next_step = std::make_shared<
      local_control_flow_historyt<track_forward_jumps, track_backward_jumps>>(
      to, decision, max_histories_per_location);
  }
  else if(
    current_loc->is_function_call() &&
    std::next(this->current_loc)->location_number != to->location_number)
  {
    // Because the history is local (to avoid massive explosion in work)
    // the history at function start should be a merge of all callers.
    // As we dont' need to enforce the number of histories we return directly.
    if(others.size() == 0)
    {
      next_step = std::make_shared<
        local_control_flow_historyt<track_forward_jumps, track_backward_jumps>>(
        to, nullptr, max_histories_per_location);
      return std::make_pair(ai_history_baset::step_statust::NEW, next_step);
    }
    else
    {
      INVARIANT(
        others.size() == 1,
        "Function start should have at most one merged history");
      INVARIANT(
        to_local_control_flow_history(*(others.begin()))
          ->is_path_merge_history(),
        "The one history must be a merge point");

      return std::make_pair(
        ai_history_baset::step_statust::MERGED, *(others.begin()));
    }
  }
  else if(current_loc->is_end_function())
  {
    // This is slightly complicated as we have to drop the current,
    // callee history and pick up the caller history.
    PRECONDITION(caller_hist != ai_history_baset::no_caller_history);

    next_step = std::make_shared<
      local_control_flow_historyt<track_forward_jumps, track_backward_jumps>>(
      to,
      to_local_control_flow_history(caller_hist)->control_flow_decision_history,
      max_histories_per_location);
  }
  else
  {
    // No changes to be made to the control_flow_decision_history
    // Is a local step forward with no branching (or a skipped function call).
    next_step = std::make_shared<
      local_control_flow_historyt<track_forward_jumps, track_backward_jumps>>(
      to, control_flow_decision_history, max_histories_per_location);
  }
  INVARIANT(
    next_step != nullptr, "All branches should create a candidate history");

  // Now check whether this already exists
  auto it = others.find(next_step);
  if(it == others.end())
  {
    if(has_histories_per_location_limit())
    {
      auto number_of_histories = others.size();

      if(number_of_histories < max_histories_per_location - 1)
      {
        // Still below limit so we can add one
        return std::make_pair(ai_history_baset::step_statust::NEW, next_step);
      }
      else if(number_of_histories == max_histories_per_location - 1)
      {
        // Last space --> we must create the merged history
        next_step = std::make_shared<local_control_flow_historyt<
          track_forward_jumps,
          track_backward_jumps>>(to, nullptr, max_histories_per_location);
        return std::make_pair(ai_history_baset::step_statust::NEW, next_step);
      }
      else if(others.size() == max_histories_per_location)
      {
        // Already at limit, need to return the merged history

        // This relies on operator< sorting null after other pointers
        auto last_history_pointer = std::prev(others.end());

        INVARIANT(
          to_local_control_flow_history(*last_history_pointer)
            ->is_path_merge_history(),
          "The last history must be the merged one");

        return std::make_pair(
          ai_history_baset::step_statust::MERGED, *last_history_pointer);
      }
      else
      {
        INVARIANT(
          others.size() <= max_histories_per_location,
          "Histories-per-location limit should be enforced");
      }
    }
    else
    {
      // No limit so ...
      return std::make_pair(ai_history_baset::step_statust::NEW, next_step);
    }
  }
  else
  {
    // An equivalent history is already available so return that
    return std::make_pair(ai_history_baset::step_statust::MERGED, *it);
  }
  UNREACHABLE;
}

template <bool track_forward_jumps, bool track_backward_jumps>
bool local_control_flow_historyt<track_forward_jumps, track_backward_jumps>::
operator<(const ai_history_baset &op) const
{
  auto other = dynamic_cast<
    const local_control_flow_historyt<track_forward_jumps, track_backward_jumps>
      &>(op);

  // Primary sort on the current location because it is fast, clusters relevant
  // things. The side effect is that this can give depth-first search which may
  // not be that "fair" when limiting the histories per location.
  if(this->current_loc->location_number < other.current_loc->location_number)
  {
    return true;
  }
  else if(
    this->current_loc->location_number > other.current_loc->location_number)
  {
    return false;
  }
  else
  {
    if(
      this->control_flow_decision_history ==
      other.control_flow_decision_history)
    {
      // They are equal so...
      return false;
    }
    else if(other.control_flow_decision_history == nullptr)
    {
      // Special case so that the merged control flow history is last step's
      // others set also means that non-merged histories are strictly preferred
      // on the work queue
      return true;
    }
    else if(this->control_flow_decision_history == nullptr)
    {
      // Another one, also guarding what we are about to do...
      return false;
    }
    else
    {
      return (
        *(this->control_flow_decision_history) <
        *(other.control_flow_decision_history));
    }
  }
  UNREACHABLE;
}

template <bool track_forward_jumps, bool track_backward_jumps>
bool local_control_flow_historyt<track_forward_jumps, track_backward_jumps>::
operator==(const ai_history_baset &op) const
{
  auto other = dynamic_cast<
    const local_control_flow_historyt<track_forward_jumps, track_backward_jumps>
      &>(op);

  // Make the short-cutting clear
  if(this->current_loc->location_number == other.current_loc->location_number)
  {
    if(
      this->control_flow_decision_history ==
      other.control_flow_decision_history)
    {
      return true;
    }
    else if(
      this->control_flow_decision_history == nullptr ||
      other.control_flow_decision_history == nullptr)
    {
      // Only one is null so clearly can't be equal
      return false;
    }
    else
    {
      // Don't have unique construction so in things like step it is possible
      // to get two distinct local_control_flow_decisiont objects that are equal
      // in value.
      return (
        *(this->control_flow_decision_history) ==
        *(other.control_flow_decision_history));
    }
  }
  else
  {
    return false;
  }
  UNREACHABLE;
}

template <bool track_forward_jumps, bool track_backward_jumps>
void local_control_flow_historyt<track_forward_jumps, track_backward_jumps>::
  output(std::ostream &out) const
{
  out << "local_control_flow_history : location "
      << current_loc->location_number;
  lcfd_ptrt working = control_flow_decision_history;
  while(working != nullptr)
  {
    out << " after " << working->branch_location->location_number;
    if(working->branch_taken)
    {
      out << " taken";
    }
    else
    {
      out << " not taken";
    }
    working = working->previous;
  }
  return;
}

bool local_control_flow_decisiont::
operator<(const local_control_flow_decisiont &op) const
{
  // Lower locations first, generally this means depth first
  if(
    this->branch_location->location_number <
    op.branch_location->location_number)
  {
    return true;
  }
  else if(
    this->branch_location->location_number >
    op.branch_location->location_number)
  {
    return false;
  }
  else
  {
    INVARIANT(
      this->branch_location->location_number ==
        op.branch_location->location_number,
      "Implied by if-then-else");

    if(!this->branch_taken && op.branch_taken)
    {
      return true; // Branch not taken takes priority
    }
    else if(this->branch_taken && !op.branch_taken)
    {
      return false; // The reverse case of above
    }
    else
    {
      INVARIANT(
        this->branch_taken == op.branch_taken, "Implied by if-then-else");

      if(this->previous == op.previous)
      {
        return false; // They are the same decision chain
      }
      else if(this->previous == nullptr)
      {
        // This prioritises complete histories over merged ones
        return false;
      }
      else if(op.previous == nullptr)
      {
        // Again, the reverse
        return true;
      }
      else
      {
        // Neither is null so sort by recursing along the list
        return *(this->previous) < *(op.previous);
      }
    }
  }
  UNREACHABLE;
}

bool local_control_flow_decisiont::
operator==(const local_control_flow_decisiont &op) const
{
  // Compare location numbers because we can't be sure that
  // both location iterators are from the same function
  // and so the iterators may not be comparable
  if(
    this->branch_location->location_number ==
    op.branch_location->location_number)
  {
    if(this->branch_taken == op.branch_taken)
    {
      if(this->previous == op.previous)
      {
        return true;
      }
      else
      {
        if((this->previous != nullptr) && (op.previous != nullptr))
        {
          return *(this->previous) == *(op.previous);
        }
      }
    }
  }
  return false;
}

// Instantiate the versions we need
template ai_history_baset::step_returnt
local_control_flow_historyt<true, true>::step(
  locationt to,
  const trace_sett &others,
  trace_ptrt caller_hist) const;

template ai_history_baset::step_returnt
local_control_flow_historyt<true, false>::step(
  locationt to,
  const trace_sett &others,
  trace_ptrt caller_hist) const;

template ai_history_baset::step_returnt
local_control_flow_historyt<false, true>::step(
  locationt to,
  const trace_sett &others,
  trace_ptrt caller_hist) const;

template ai_history_baset::step_returnt
local_control_flow_historyt<false, false>::step(
  locationt to,
  const trace_sett &others,
  trace_ptrt caller_hist) const;
