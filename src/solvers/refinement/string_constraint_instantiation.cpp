/*******************************************************************\

Module: Defines functions related to string constraints.

Author: Jesse Sigal, jesse.sigal@diffblue.com

\*******************************************************************/

/// \file
/// Defines related function for string constraints.

#include <solvers/refinement/string_constraint_instantiation.h>

#include <solvers/refinement/string_constraint.h>
#include <solvers/refinement/string_constraint_generator.h>
#include <solvers/refinement/string_refinement.h>

/// Instantiates a quantified formula representing `not_contains` by
/// substituting the quantifiers and generating axioms.
/// \related string_refinementt
/// \param [in] axiom: the axiom to instantiate
/// \param [in] index_set0: the index set for `axiom.s0()`
/// \param [in] index_set1: the index set for `axiom.s1()`
/// \param [in] generator: generator to be used to get `axiom`'s witness
/// \return the lemmas produced through instantiation
std::vector<exprt> instantiate_not_contains(
  const string_not_contains_constraintt &axiom,
  const std::set<exprt> &index_set0,
  const std::set<exprt> &index_set1,
  const string_constraint_generatort &generator)
{
  std::vector<exprt> lemmas;

  const string_exprt s0=to_string_expr(axiom.s0());
  const string_exprt s1=to_string_expr(axiom.s1());

  for(const auto &i0 : index_set0)
    for(const auto &i1 : index_set1)
    {
      const minus_exprt val(i0, i1);
      const exprt witness=generator.get_witness_of(axiom, val);
      const and_exprt prem_and_is_witness(
        axiom.premise(),
        equal_exprt(witness, i1));

      const not_exprt differ(equal_exprt(s0[i0], s1[i1]));
      const implies_exprt lemma(prem_and_is_witness, differ);
      lemmas.push_back(lemma);

      // we put bounds on the witnesses:
      // 0 <= v <= |s0| - |s1| ==> 0 <= v+w[v] < |s0| && 0 <= w[v] < |s1|
      const exprt zero=from_integer(0, val.type());
      const binary_relation_exprt c1(zero, ID_le, plus_exprt(val, witness));
      const binary_relation_exprt c2(
        s0.length(), ID_gt, plus_exprt(val, witness));
      const binary_relation_exprt c3(s1.length(), ID_gt, witness);
      const binary_relation_exprt c4(zero, ID_le, witness);

      const minus_exprt diff(s0.length(), s1.length());

      const and_exprt premise(
        binary_relation_exprt(zero, ID_le, val),
        binary_relation_exprt(diff, ID_ge, val));
      const implies_exprt witness_bounds(
        premise,
        and_exprt(and_exprt(c1, c2), and_exprt(c3, c4)));
      lemmas.push_back(witness_bounds);
    }

  return lemmas;
}
