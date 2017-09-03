/*******************************************************************\

Module: Defines related function for string constraints.

Author: Jesse Sigal, jesse.sigal@diffblue.com

\*******************************************************************/

/// \file
/// Defines related function for string constraints.

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_INSTANTIATION_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_INSTANTIATION_H

#include <solvers/refinement/string_constraint.h>
#include <solvers/refinement/string_constraint_generator.h>

std::vector<exprt> instantiate_not_contains(
  const string_not_contains_constraintt &axiom,
  const std::set<exprt> &index_set0,
  const std::set<exprt> &index_set1,
  const string_constraint_generatort &generator);

#endif // CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_INSTANTIATION_H
