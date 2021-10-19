/*******************************************************************\

Author: Diffblue

\*******************************************************************/

/// \file
/// Utilities for printing location info steps in the trace in a format
/// agnostic way

#include "structured_trace_util.h"
#include "goto_trace.h"

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

optionalt<default_trace_stept> default_step(
  const goto_trace_stept &step,
  const source_locationt &previous_source_location)
{
  const source_locationt &source_location = step.pc->source_location();
  if(source_location.is_nil() || source_location.get_file().empty())
    return {};

  const auto default_step_kind = ::default_step_kind(*step.pc);

  // If this is just a source location then we output only the first
  // location of a sequence of same locations.
  // However, we don't want to suppress loop head locations because
  // they might come from different loop iterations. If we suppressed
  // them it would be impossible to know which loop iteration
  // we are in.
  if(
    source_location == previous_source_location &&
    default_step_kind == default_step_kindt::LOCATION_ONLY)
  {
    return {};
  }

  return default_trace_stept{default_step_kind,
                             step.hidden,
                             step.thread_nr,
                             step.step_nr,
                             source_location};
}
