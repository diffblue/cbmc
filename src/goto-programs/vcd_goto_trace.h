/*******************************************************************\

Module: Traces of GOTO Programs in VCD (Value Change Dump) Format

Author: Daniel Kroening

Date: June 2011

\*******************************************************************/

/// \file
/// Traces of GOTO Programs in VCD (Value Change Dump) Format

#ifndef CPROVER_GOTO_PROGRAMS_VCD_GOTO_TRACE_H
#define CPROVER_GOTO_PROGRAMS_VCD_GOTO_TRACE_H

#include <iosfwd>

class goto_tracet;
class namespacet;

void output_vcd(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  std::ostream &out);

#endif // CPROVER_GOTO_PROGRAMS_VCD_GOTO_TRACE_H
