/*******************************************************************\

Module: Traces of GOTO Programs

Author: Daniel Kroening

Date: July 2005

\*******************************************************************/

/// \file
/// Traces of GOTO Programs

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

// builds a trace that stops after the given step
void build_goto_trace(
  const symex_target_equationt &target,
  symex_target_equationt::SSA_stepst::const_iterator last_step_to_keep,
  const prop_convt &prop_conv,
  const namespacet &ns,
  goto_tracet &goto_trace);

typedef std::function<
  bool(symex_target_equationt::SSA_stepst::const_iterator, const prop_convt &)>
  ssa_step_predicatet;

// builds a trace that stops after the step matching a given condition
void build_goto_trace(
  const symex_target_equationt &target,
  ssa_step_predicatet stop_after_predicate,
  const prop_convt &prop_conv,
  const namespacet &ns,
  goto_tracet &goto_trace);

#endif // CPROVER_GOTO_SYMEX_BUILD_GOTO_TRACE_H
