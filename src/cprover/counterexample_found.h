/*******************************************************************\

Module: Counterexample Found

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Counterexample Found

#ifndef CPROVER_CPROVER_COUNTEREXAMPLE_FOUND_H
#define CPROVER_CPROVER_COUNTEREXAMPLE_FOUND_H

#include "solver_types.h"

#include <unordered_set>

optionalt<propertyt::tracet> counterexample_found(
  const std::vector<framet> &,
  const workt &,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  bool verbose,
  const namespacet &);

class bv_pointers_widet;

void show_assignment(const bv_pointers_widet &);

#endif // CPROVER_CPROVER_COUNTEREXAMPLE_FOUND_H
