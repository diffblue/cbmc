/*******************************************************************\

Module: Simplify State Expression

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Simplify State Expression

#ifndef CPROVER_CPROVER_SIMPLIFY_STATE_EXPR_H
#define CPROVER_CPROVER_SIMPLIFY_STATE_EXPR_H

#include <util/std_expr.h> // IWYU pragma: keep

#include <unordered_set>

class namespacet;

exprt simplify_state_expr(
  exprt,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &);

exprt simplify_state_expr_node(
  exprt,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &);

#endif // CPROVER_CPROVER_PROPAGATE_H
