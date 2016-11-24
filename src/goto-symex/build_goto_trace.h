/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

Date: July 2005

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_BUILD_GOTO_TRACE_H
#define CPROVER_GOTO_SYMEX_BUILD_GOTO_TRACE_H

#include "symex_target_equation.h"
#include "goto_symex_state.h"

// builds a trace that stops at first failing assertion
void build_goto_trace(
  const symex_target_equationt &target,
  const prop_convt &prop_conv,
  const namespacet &ns,
  goto_tracet &goto_trace);

// builds a trace that stops after given step
void build_goto_trace(
  const symex_target_equationt &target,
  symex_target_equationt::SSA_stepst::const_iterator stop,
  const prop_convt &prop_conv,
  const namespacet &ns,
  goto_tracet &goto_trace);

#endif
