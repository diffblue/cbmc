/*******************************************************************\

Module: Build Goto Trace from Path Symex History

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PATH_SYMEX_BUILD_GOTO_TRACE_H
#define CPROVER_PATH_SYMEX_BUILD_GOTO_TRACE_H

#include <util/decision_procedure.h>
#include <goto-programs/goto_trace.h>

#include "path_symex_state.h"

void build_goto_trace(
  const path_symex_statet &state,
  const decision_proceduret &decision_procedure,
  goto_tracet &goto_trace);

#endif
