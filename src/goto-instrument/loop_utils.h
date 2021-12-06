/*******************************************************************\

Module: Helper functions for k-induction and loop invariants

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Helper functions for k-induction and loop invariants

#ifndef CPROVER_GOTO_INSTRUMENT_LOOP_UTILS_H
#define CPROVER_GOTO_INSTRUMENT_LOOP_UTILS_H

#include <analyses/natural_loops.h>

class local_may_aliast;

typedef std::set<exprt> assignst;
typedef natural_loops_mutablet::natural_loopt loopt;

void get_assigns(
  const local_may_aliast &local_may_alias,
  const loopt &loop,
  assignst &assigns);

void get_assigns_lhs(
  const local_may_aliast &local_may_alias,
  goto_programt::const_targett t,
  const exprt &lhs,
  assignst &assigns);

goto_programt::targett get_loop_exit(const loopt &);

#endif // CPROVER_GOTO_INSTRUMENT_LOOP_UTILS_H
