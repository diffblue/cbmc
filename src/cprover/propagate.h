/*******************************************************************\

Module: Propagate

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Propagate

#ifndef CPROVER_CPROVER_PROPAGATE_H
#define CPROVER_CPROVER_PROPAGATE_H

#include "solver_types.h"

#include <unordered_set>

void propagate(
  const std::vector<framet> &,
  const workt &,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  bool verbose,
  const namespacet &,
  const std::function<void(const symbol_exprt &, exprt, const workt::patht &)>
    &propagator);

exprt simplify_state_expr(
  exprt,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &);

exprt simplify_state_expr_node(
  exprt,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  const namespacet &);

#endif // CPROVER_CPROVER_PROPAGATE_H
