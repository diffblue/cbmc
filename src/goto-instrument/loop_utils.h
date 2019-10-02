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

typedef std::set<exprt> modifiest;
typedef natural_loops_mutablet::natural_loopt loopt;

void get_modifies(
  const local_may_aliast &local_may_alias,
  const loopt &loop,
  modifiest &modifies);

void get_modifies_lhs(
  const local_may_aliast &local_may_alias,
  goto_programt::const_targett t,
  const exprt &lhs,
  modifiest &modifies);

void build_havoc_code(
  const goto_programt::targett loop_head,
  const modifiest &modifies,
  goto_programt &dest);

goto_programt::targett get_loop_exit(const loopt &);

#endif // CPROVER_GOTO_INSTRUMENT_LOOP_UTILS_H
