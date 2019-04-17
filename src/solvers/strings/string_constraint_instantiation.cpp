/*******************************************************************\

Module: Defines functions related to string constraints.

Author: Jesse Sigal, jesse.sigal@diffblue.com

\*******************************************************************/

/// \file
/// Defines related function for string constraints.

#include "string_constraint_instantiation.h"
#include <algorithm>
#include <unordered_set>
#include <util/expr_iterator.h>

/// Look for symbol \p qvar in the expression \p index and return true if found
/// \return True, iff \p qvar appears in \p index.
static bool contains(const exprt &index, const symbol_exprt &qvar)
{
  return std::find(index.depth_begin(), index.depth_end(), qvar) !=
         index.depth_end();
}

/// Find indexes of `str` used in `expr` that contains `qvar`, for instance
/// with arguments ``(str[k+1]=='a')``, `str`, and `k`, the function should
/// return `k+1`.
/// \param [in] expr: the expression to search
/// \param [in] str: the string which must be indexed
/// \param [in] qvar: the universal variable that must be in the index
/// \return index expressions in `expr` on `str` containing `qvar`.
static std::unordered_set<exprt, irep_hash>
find_indexes(const exprt &expr, const exprt &str, const symbol_exprt &qvar)
{
  decltype(find_indexes(expr, str, qvar)) result;
  auto index_str_containing_qvar = [&](const exprt &e) {
    if(auto index_expr = expr_try_dynamic_cast<index_exprt>(e))
    {
      const auto &arr = index_expr->array();
      const auto str_it = std::find(arr.depth_begin(), arr.depth_end(), str);
      return str_it != arr.depth_end() && contains(index_expr->index(), qvar);
    }
    return false;
  };

  std::for_each(expr.depth_begin(), expr.depth_end(), [&](const exprt &e) {
    if(index_str_containing_qvar(e))
      result.insert(to_index_expr(e).index());
  });
  return result;
}

std::map<exprt, int> map_representation_of_sum(const exprt &f)
{
  // number of times the leaf should be added (can be negative)
  std::map<exprt, int> elems;

  std::list<std::pair<exprt, bool>> to_process;
  to_process.emplace_back(f, true);

  while(!to_process.empty())
  {
    exprt cur = to_process.back().first;
    bool positive = to_process.back().second;
    to_process.pop_back();
    if(cur.id() == ID_plus)
    {
      for(const auto &op : cur.operands())
        to_process.emplace_back(op, positive);
    }
    else if(cur.id() == ID_minus)
    {
      to_process.emplace_back(cur.op1(), !positive);
      to_process.emplace_back(cur.op0(), positive);
    }
    else if(cur.id() == ID_unary_minus)
    {
      to_process.emplace_back(cur.op0(), !positive);
    }
    else
    {
      if(positive)
        ++elems[cur];
      else
        --elems[cur];
    }
  }
  return elems;
}

exprt sum_over_map(std::map<exprt, int> &m, const typet &type, bool negated)
{
  if(m.empty())
    return from_integer(0, type);

  exprt sum = nil_exprt();
  mp_integer constants = 0;
  typet index_type = m.begin()->first.type();

  for(const auto &term : m)
  {
    const exprt &t = term.first;
    int factor = negated ? (-term.second) : term.second;
    if(t.id() == ID_constant)
    {
      // Constants are accumulated in the variable \c constants
      const auto int_value = numeric_cast_v<mp_integer>(to_constant_expr(t));
      constants += int_value * factor;
    }
    else
    {
      switch(factor)
      {
      case -1:
        if(sum.is_nil())
          sum = unary_minus_exprt(t);
        else
          sum = minus_exprt(sum, t);
        break;

      case 1:
        if(sum.is_nil())
          sum = t;
        else
          sum = plus_exprt(sum, t);
        break;

      default:
        if(factor > 1)
        {
          if(sum.is_nil())
            sum = t;
          else
            sum = plus_exprt(sum, t);
          for(int i = 1; i < factor; i++)
            sum = plus_exprt(sum, t);
        }
        else if(factor < -1)
        {
          if(sum.is_nil())
            sum = unary_minus_exprt(t);
          else
            sum = minus_exprt(sum, t);
          for(int i = -1; i > factor; i--)
            sum = minus_exprt(sum, t);
        }
      }
    }
  }

  const exprt index_const = from_integer(constants, index_type);
  if(sum.is_not_nil())
    return plus_exprt(sum, index_const);
  else
    return index_const;
}

/// \param qvar: a symbol representing a universally quantified variable
/// \param val: an expression
/// \param f: an expression containing `+` and `-`
///   operations in which `qvar` should appear exactly once.
/// \return an expression corresponding of $f^{-1}(val)$ where $f$ is seen as
///   a function of $qvar$, i.e. the value that is necessary for `qvar` for `f`
///   to be equal to `val`. For instance, if `f` corresponds to the expression
///   $q + x$, `compute_inverse_function(q,v,f)` returns an expression
///   for $v - x$.
static exprt
compute_inverse_function(const exprt &qvar, const exprt &val, const exprt &f)
{
  exprt positive, negative;
  // number of time the element should be added (can be negative)
  // qvar has to be equal to val - f(0) if it appears positively in f
  // (i.e. if f(qvar)=f(0) + qvar) and f(0) - val if it appears negatively
  // in f. So we start by computing val - f(0).
  std::map<exprt, int> elems = map_representation_of_sum(minus_exprt(val, f));

  // true if qvar appears negatively in f (positively in elems):
  bool neg = false;

  auto it = elems.find(qvar);
  INVARIANT(
    it != elems.end(),
    string_refinement_invariantt("a function must have an occurrence of qvar"));
  if(it->second == 1 || it->second == -1)
  {
    neg = (it->second == 1);
  }
  else
  {
    INVARIANT(
      it->second == 0,
      string_refinement_invariantt(
        "a proper function must have exactly one "
        "occurrences after reduction, or it cancelled out, and it does not"
        " have one"));
  }

  elems.erase(it);
  return sum_over_map(elems, f.type(), neg);
}

/// Instantiates a string constraint by substituting the quantifiers.
/// For a string constraint of the form `forall q. P(x)`,
/// substitute `q` the universally quantified variable of `axiom`, by
/// an `index`, in `axiom`, so that the index used for `str` equals `val`.
/// For instance, if `axiom` is `forall q. s[q+x] = 'a' && t[q] = 'b'`,
/// `instantiate(axiom,s,v)` would return the expression
/// `s[v] = 'a' && t[v-x] = 'b'`.
/// If there are several such indexes, the conjunction of the instantiations is
/// returned, for instance for a formula:
/// `forall q. s[q+x]='a' && s[q]=c` we would get
/// `s[v] = 'a' && s[v-x] = c && s[v+x] = 'a' && s[v] = c`.
/// \param axiom: a universally quantified formula
/// \param str: an array of characters
/// \param val: an index expression
/// \return instantiated formula
exprt
instantiate(const string_constraintt &axiom, const exprt &str, const exprt &val)
{
  exprt::operandst conjuncts;
  for(const auto &index : find_indexes(axiom.body, str, axiom.univ_var))
  {
    const exprt univ_var_value =
      compute_inverse_function(axiom.univ_var, val, index);
    implies_exprt instance(
      and_exprt(
    binary_relation_exprt(axiom.univ_var, ID_ge, axiom.lower_bound),
    binary_relation_exprt(axiom.univ_var, ID_lt, axiom.upper_bound)),
    axiom.body);
    replace_expr(axiom.univ_var, univ_var_value, instance);
    conjuncts.push_back(instance);
  }
  return conjunction(conjuncts);
}

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
    const exprt &i0 = pair.first;
    const exprt &i1 = pair.second;
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
