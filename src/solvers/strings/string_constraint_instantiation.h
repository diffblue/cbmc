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

/// Substitute `qvar` the universally quantified variable of `axiom`, by
/// an index `val`, in `axiom`, so that the index used for `str` equals `val`.
/// For instance, if `axiom` corresponds to \f$\forall q.\ s[q+x]='a' \land
/// t[q]='b'\f$, `instantiate(axiom,s,v)` would return an expression for
/// \f$s[v]='a' \land t[v-x]='b'\f$.
/// \param axiom: a universally quantified formula
/// \param str: an array of char variable
/// \param val: an index expression
/// \return `axiom` with substitued `qvar`
exprt instantiate(
  const string_constraintt &axiom,
  const exprt &str,
  const exprt &val);

std::vector<exprt> instantiate_not_contains(
  const string_not_contains_constraintt &axiom,
  const std::set<std::pair<exprt, exprt>> &index_pairs,
  const std::unordered_map<string_not_contains_constraintt, symbol_exprt>
    &witnesses);

/// \param f: an expression with only addition and subtraction
/// \return a map where each leaf of the input is mapped to the number of times
///   it is added. For instance, expression $x + x - y + 3 - 5$ would give the
///   map x -> 2, y -> -1, 3 -> 1, 5 -> -1.
std::map<exprt, int> map_representation_of_sum(const exprt &f);

/// \param m: a map from expressions to integers
/// \param type: type for the returned expression
/// \param negated: optinal Boolean asking to negates the sum
/// \return a expression for the sum of each element in the map a number of
///   times given by the corresponding integer in the map. For a map x -> 2, y
///   -> -1 would give an expression $x + x - y$.
exprt sum_over_map(
  std::map<exprt, int> &m,
  const typet &type,
  bool negated = false);

#endif // CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_INSTANTIATION_H
