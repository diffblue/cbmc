/*******************************************************************\

Module: Traces of GOTO Programs in VCD (Value Change Dump) Format

Author: Daniel Kroening

Date: June 2011

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_VCD_GOTO_TRACE_H
#define CPROVER_GOTO_SYMEX_VCD_GOTO_TRACE_H

#include <iostream>

#include <namespace.h>

#include "goto_trace.h"

void output_vcd(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  std::ostream &out);

#endif
