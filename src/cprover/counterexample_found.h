/*******************************************************************\

Module: Counterexample Found

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Counterexample Found

#ifndef CPROVER_CPROVER_COUNTEREXAMPLE_FOUND_H
#define CPROVER_CPROVER_COUNTEREXAMPLE_FOUND_H

#include "solver_types.h"

#include <string>
#include <unordered_set>

std::optional<propertyt::tracet> counterexample_found(
  const std::vector<framet> &,
  const workt &,
  const std::unordered_set<symbol_exprt, irep_hash> &address_taken,
  bool verbose,
  const namespacet &,
  const std::string &smt2_solver_binary = "");

class decision_proceduret;

void show_assignment(const decision_proceduret &);

#endif // CPROVER_CPROVER_COUNTEREXAMPLE_FOUND_H
