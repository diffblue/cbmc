/*******************************************************************\

Author: Diffblue

\*******************************************************************/

/// \file
/// Utilities for printing location info steps in the trace in a format
/// agnostic way

#ifndef CPROVER_GOTO_PROGRAMS_STRUCTURED_TRACE_UTIL_H
#define CPROVER_GOTO_PROGRAMS_STRUCTURED_TRACE_UTIL_H

#include "goto_program.h"
#include <string>

/// There are two kinds of step for location markers - location-only and
/// loop-head (for locations associated with the first step of a loop).
enum class default_step_kindt
{
  LOCATION_ONLY,
  LOOP_HEAD
};

/// Identify for a given instruction whether it is a loophead or just a location
///
/// Loopheads are determined by whether there is backwards jump to them. This
/// matches the loop detection used for loop IDs
/// \param instruction: The instruction to inspect.
/// \return LOOP_HEAD if this is a loop head, otherwise LOCATION_ONLY
default_step_kindt
default_step_kind(const goto_programt::instructiont &instruction);

/// Turns a \ref default_step_kindt into a string that can be used in the trace
/// \param step_type: The kind of step, deduced from \ref default_step_kind
/// \return  Either "loop-head" or "location-only"
std::string default_step_name(const default_step_kindt &step_type);

#endif // CPROVER_GOTO_PROGRAMS_STRUCTURED_TRACE_UTIL_H
