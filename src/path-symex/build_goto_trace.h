/*******************************************************************\

Module: Build Goto Trace from State History

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BUILD_GOTO_TRACE_H
#define CPROVER_BUILD_GOTO_TRACE_H

#include <util/decision_procedure.h>

#include <goto-programs/goto_trace.h>

#include <path-symex/locs.h>

#include "state.h"

void build_goto_trace(
  const locst &locs,
  const statet &state,
  const decision_proceduret &decision_procedure,
  const namespacet &ns,
  goto_tracet &goto_trace);

#endif
