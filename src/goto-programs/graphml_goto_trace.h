/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

Date: January 2015

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GRAPHML_GOTO_TRACE_H
#define CPROVER_GOTO_PROGRAMS_GRAPHML_GOTO_TRACE_H

#include <xmllang/graphml.h>

#include "goto_trace.h"

void convert(
  const namespacet &ns,
  const goto_tracet &goto_trace,
  graphmlt &graphml);

#endif
