/*******************************************************************\

Module: Defines related function for string constraints.

Author: Jesse Sigal, jesse.sigal@diffblue.com

\*******************************************************************/

/// \file
/// Defines related function for string constraints.

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_INSTANTIATION_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_INSTANTIATION_H

#include "string_constraint.h"
#include "string_constraint_generator.h"

std::vector<exprt> instantiate_not_contains(
  const string_not_contains_constraintt &axiom,
  const std::set<std::pair<exprt, exprt>> &index_pairs,
  const std::unordered_map<string_not_contains_constraintt, symbol_exprt>
    &witnesses);

#endif // CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_INSTANTIATION_H
