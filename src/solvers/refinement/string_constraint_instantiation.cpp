/*******************************************************************\

Module: Defines functions related to string constraints.

Author: Jesse Sigal, jesse.sigal@diffblue.com

\*******************************************************************/

/// \file
/// Defines related function for string constraints.

#include <solvers/refinement/string_constraint_instantiation.h>

/// Instantiates a quantified formula representing `not_contains` by
/// substituting the quantifiers and generating axioms.
/// \related string_refinementt
/// \param [in] axiom: the axiom to instantiate
/// \param [in] index_pairs: pair of indexes for `axiom.s0()`and `axiom.s1()`
/// \param [in] witnesses: `axiom`'s witnesses for non containment
/// \return the lemmas produced through instantiation
std::vector<exprt> instantiate_not_contains(
  const string_not_contains_constraintt &axiom,
  const std::set<std::pair<exprt, exprt>> &index_pairs,
  const std::unordered_map<string_not_contains_constraintt, symbol_exprt>
    &witnesses)
{
  std::vector<exprt> lemmas;

  const array_string_exprt s0 = axiom.s0;
  const array_string_exprt s1 = axiom.s1;

  for(const auto &pair : index_pairs)
  {
    // We have s0[x+f(x)] and s1[f(x)], so to have i0 indexing s0 and i1
    // indexing s1, we need x = i0 - i1 and f(i0 - i1) = f(x) = i1.
    const exprt &i0=pair.first;
    const exprt &i1=pair.second;
    const minus_exprt val(i0, i1);
    const and_exprt universal_bound(
      binary_relation_exprt(axiom.univ_lower_bound, ID_le, val),
      binary_relation_exprt(axiom.univ_upper_bound, ID_gt, val));
    const exprt f = index_exprt(witnesses.at(axiom), val);
    const equal_exprt relevancy(f, i1);
    const and_exprt premise(relevancy, axiom.premise, universal_bound);

    const notequal_exprt differ(s0[i0], s1[i1]);
    const and_exprt existential_bound(
      binary_relation_exprt(axiom.exists_lower_bound, ID_le, i1),
      binary_relation_exprt(axiom.exists_upper_bound, ID_gt, i1));
    const and_exprt body(differ, existential_bound);

    const implies_exprt lemma(premise, body);
    lemmas.push_back(lemma);
  }

  return lemmas;
}
