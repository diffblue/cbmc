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
/// \param [in] index_pairs: the pairs of indices to at which to instantiate
/// \param [in] generator: generator to be used to get `axiom`'s witness
/// \return the lemmas produced through instantiation
std::vector<exprt> instantiate_not_contains(
  const string_not_contains_constraintt &axiom,
  const std::set<std::pair<exprt, exprt>> &index_pairs,
  const string_constraint_generatort &generator)
{
  std::vector<exprt> lemmas;

  const string_exprt &s0=to_string_expr(axiom.s0());
  const string_exprt &s1=to_string_expr(axiom.s1());

  for(const auto &pair : index_pairs)
  {
    // We have s0[x+f(x)] and s1[f(x)], so to have i0 indexing s0 and i1
    // indexing s1, we need x = i0 - i1 and f(i0 - i1) = f(x) = i1.
    const exprt &i0=pair.first;
    const exprt &i1=pair.second;
    const minus_exprt val(i0, i1);
    const and_exprt universal_bound(
      binary_relation_exprt(axiom.univ_lower_bound(), ID_le, val),
      binary_relation_exprt(axiom.univ_upper_bound(), ID_gt, val));
    const exprt f=generator.get_witness_of(axiom, val);
    const equal_exprt relevancy(f, i1);
    const and_exprt premise(relevancy, axiom.premise(), universal_bound);

    const notequal_exprt differ(s0[i0], s1[i1]);
    const and_exprt existential_bound(
      binary_relation_exprt(axiom.exists_lower_bound(), ID_le, i1),
      binary_relation_exprt(axiom.exists_upper_bound(), ID_gt, i1));
    const and_exprt body(differ, existential_bound);

    const implies_exprt lemma(premise, body);
    lemmas.push_back(lemma);
  }

  return lemmas;
}
