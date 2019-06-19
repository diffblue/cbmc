/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Symbolic Execution of assignments

#ifndef CPROVER_GOTO_SYMEX_SYMEX_ASSIGN_H
#define CPROVER_GOTO_SYMEX_SYMEX_ASSIGN_H

#include "symex_target.h"
#include <util/expr.h>

class goto_symex_statet;
class ssa_exprt;
struct symex_configt;

/// Record the assignment of value \p rhs to variable \p lhs in \p state and add
/// the equation to target: `lhs#{n+1} == guard ? rhs#{m} : lhs#{n}`
/// where {n} and {m} denote the current L2 indexes of lhs and rhs respectively.
void symex_assign_symbol(
  goto_symex_statet &state,
  const ssa_exprt &lhs, // L1
  const exprt &full_lhs,
  const exprt &rhs,
  const exprt::operandst &guard,
  symex_targett::assignment_typet assignment_type,
  const namespacet &ns,
  const symex_configt &symex_config,
  symex_targett &target);

void symex_assign_rec(
  goto_symex_statet &state,
  const exprt &lhs,
  const exprt &full_lhs,
  const exprt &rhs,
  exprt::operandst &guard,
  symex_targett::assignment_typet assignment_type,
  const namespacet &ns,
  const symex_configt &symex_config,
  symex_targett &target);

#endif // CPROVER_GOTO_SYMEX_SYMEX_ASSIGN_H
