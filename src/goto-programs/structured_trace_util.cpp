/*******************************************************************\

Author: Diffblue

\*******************************************************************/

/// \file
/// Utilities for printing location info steps in the trace in a format
/// agnostic way

#include "structured_trace_util.h"
#include <algorithm>

default_step_kindt
default_step_kind(const goto_programt::instructiont &instruction)
{
  const bool is_loophead = std::any_of(
    instruction.incoming_edges.begin(),
    instruction.incoming_edges.end(),
    [](goto_programt::targett t) { return t->is_backwards_goto(); });

  return is_loophead ? default_step_kindt::LOOP_HEAD
                     : default_step_kindt::LOCATION_ONLY;
}
std::string default_step_name(const default_step_kindt &step_type)
{
  switch(step_type)
  {
  case default_step_kindt::LOCATION_ONLY:
    return "location-only";
  case default_step_kindt::LOOP_HEAD:
    return "loop-head";
  }
  UNREACHABLE;
}
