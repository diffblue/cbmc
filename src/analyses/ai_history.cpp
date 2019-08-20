/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Abstract Interpretation history

#include "ai_history.h"

jsont ai_history_baset::output_json(void) const
{
  std::ostringstream out;
  output(out);
  json_stringt json(out.str());
  return std::move(json);
}

xmlt ai_history_baset::output_xml(void) const
{
  std::ostringstream out;
  output(out);
  xmlt xml("history");
  xml.data = out.str();
  return xml;
}

ai_history_baset::step_returnt
call_stack_historyt::step(locationt to, const trace_sett &others) const
{
  DATA_INVARIANT(current_stack != nullptr, "current_stack must exist");

  cse_ptrt next_stack = nullptr;

  // First construct what the new history would be.
  // This requires special handling if this edge is a function call or return
  if(current_stack->current_location->is_function_call())
  {
    locationt l_return = std::next(current_stack->current_location);

    if(l_return->location_number == to->location_number)
    {
      // Is skipping the function call, only update the location
      next_stack =
        cse_ptrt(new call_stack_entryt(l_return, current_stack->caller));
    }
    else
    {
      // An interprocedural (call) edge; add to the current stack
      next_stack = cse_ptrt(new call_stack_entryt(to, current_stack));
    }
  }
  else if(current_stack->current_location->is_end_function())
  {
    if(current_stack->caller == nullptr)
    {
      // Trying to return but there was no caller?
      // Refuse to do the transition outright
      return std::make_pair(ai_history_baset::step_statust::BLOCKED, nullptr);
    }
    else
    {
      // The expected call return site...
      locationt l_caller_return =
        std::next(current_stack->caller->current_location);

      if(l_caller_return->location_number == to->location_number)
      {
        // ... which is where we are going
        next_stack =
          cse_ptrt(new call_stack_entryt(to, current_stack->caller->caller));
      }
      else
      {
        // Not possible to return to somewhere other than the call site
        return std::make_pair(ai_history_baset::step_statust::BLOCKED, nullptr);
      }
    }
  }
  else
  {
    // Just update the location
    next_stack = cse_ptrt(new call_stack_entryt(to, current_stack->caller));
  }
  INVARIANT(next_stack != nullptr, "All branches should initialise next_stack");

  // Create the potential next history
  trace_ptrt next(new call_stack_historyt(next_stack));

  // If there is already an equivalent history, merge with that instead
  auto it = others.find(next);

  if(it == others.end())
  {
    return std::make_pair(ai_history_baset::step_statust::NEW, next);
  }
  else
  {
    return std::make_pair(ai_history_baset::step_statust::MERGED, *it);
  }
}

bool call_stack_historyt::operator<(const ai_history_baset &op) const
{
  auto other = dynamic_cast<const call_stack_historyt *>(&op);
  PRECONDITION(other != nullptr);

  return *(this->current_stack) < *(other->current_stack);
}

bool call_stack_historyt::operator==(const ai_history_baset &op) const
{
  auto other = dynamic_cast<const call_stack_historyt *>(&op);
  PRECONDITION(other != nullptr);

  return *(this->current_stack) == *(other->current_stack);
}

void call_stack_historyt::output(std::ostream &out) const
{
  out << "call_stack_history : stack "
      << current_stack->current_location->location_number;
  cse_ptrt working = current_stack->caller;
  while(working != nullptr)
  {
    out << " from " << working->current_location->location_number;
    working = working->caller;
  }
  return;
}

bool call_stack_historyt::call_stack_entryt::
operator<(const call_stack_entryt &op) const
{
  if(
    this->current_location->location_number <
    op.current_location->location_number)
  {
    return true;
  }
  else if(
    this->current_location->location_number >
    op.current_location->location_number)
  {
    return false;
  }
  else
  {
    INVARIANT(
      this->current_location->location_number ==
        op.current_location->location_number,
      "Implied by if-then-else");

    if(this->caller == op.caller)
    {
      return false; // Because they are equal
    }
    else if(this->caller == nullptr)
    {
      return true; // Shorter stacks are 'lower'
    }
    else if(op.caller == nullptr)
    {
      return false;
    }
    else
    {
      // Sort by the rest of the stack
      return *(this->caller) < *(op.caller);
    }
  }
  UNREACHABLE;
}

bool call_stack_historyt::call_stack_entryt::
operator==(const call_stack_entryt &op) const
{
  if(
    this->current_location->location_number ==
    op.current_location->location_number)
  {
    if(this->caller == op.caller)
    {
      return true;
    }
    else if(this->caller != nullptr && op.caller != nullptr)
    {
      return *(this->caller) == *(op.caller);
    }
  }
  return false;
}
