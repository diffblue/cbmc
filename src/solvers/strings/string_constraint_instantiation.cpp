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

linear_functiont::linear_functiont(const exprt &f)
{
  type = f.type();
  // list of expressions to process with a boolean flag telling whether they
  // appear positively or negatively (true is for positive)
  std::list<std::pair<exprt, bool>> to_process;
  to_process.emplace_back(f, true);

  while(!to_process.empty())
  {
    const exprt cur = to_process.back().first;
    bool positive = to_process.back().second;
    to_process.pop_back();
    if(auto integer = numeric_cast<mp_integer>(cur))
    {
      constant_coefficient += positive ? integer.value() : -integer.value();
    }
    else if(cur.id() == ID_plus)
    {
      for(const auto &op : cur.operands())
        to_process.emplace_back(op, positive);
    }
    else if(cur.id() == ID_minus)
    {
      to_process.emplace_back(to_minus_expr(cur).op1(), !positive);
      to_process.emplace_back(to_minus_expr(cur).op0(), positive);
    }
    else if(cur.id() == ID_unary_minus)
    {
      to_process.emplace_back(to_unary_minus_expr(cur).op(), !positive);
    }
    else
    {
      if(positive)
        ++coefficients[cur];
      else
        --coefficients[cur];
    }
  }
}

void linear_functiont::add(const linear_functiont &other)
{
  PRECONDITION(type == other.type);
  constant_coefficient += other.constant_coefficient;
  for(auto pair : other.coefficients)
    coefficients[pair.first] += pair.second;
}

exprt linear_functiont::to_expr(bool negated) const
{
  exprt sum = nil_exprt{};
  const exprt constant_expr = from_integer(constant_coefficient, type);
  if(constant_coefficient != 0)
    sum = negated ? (exprt)unary_minus_exprt{constant_expr} : constant_expr;

  for(const auto &term : coefficients)
  {
    const exprt &t = term.first;
    const mp_integer factor = negated ? (-term.second) : term.second;
    if(factor == -1)
    {
      if(sum.is_nil())
        sum = unary_minus_exprt(t);
      else
        sum = minus_exprt(sum, t);
    }
    else if(factor == 1)
    {
      if(sum.is_nil())
        sum = t;
      else
        sum = plus_exprt(sum, t);
    }
    else if(factor != 0)
    {
      const mult_exprt to_add{t, from_integer(factor, t.type())};
      if(sum.is_nil())
        sum = to_add;
      else
        sum = plus_exprt(sum, to_add);
    }
  }
  return sum.is_nil() ? from_integer(0, type) : sum;
}

exprt linear_functiont::solve(
  linear_functiont f,
  const exprt &var,
  const exprt &val)
{
  auto it = f.coefficients.find(var);
  PRECONDITION(it != f.coefficients.end());
  PRECONDITION(it->second == 1 || it->second == -1);
  const bool positive = it->second == 1;

  // Transform `f` into `f(var <- 0)`
  f.coefficients.erase(it);
  // Transform `f(var <- 0)` into `f(var <- 0) - val`
  f.add(linear_functiont{unary_minus_exprt{val}});

  // If the coefficient of var is 1 then solution `val - f(var <- 0),
  // otherwise `f(var <- 0) - val`
  return f.to_expr(positive);
}

std::string linear_functiont::format()
{
  std::ostringstream stream;
  stream << constant_coefficient;
  for(const auto &pair : coefficients)
    stream << " + " << pair.second << " * " << ::format(pair.first);
  return stream.str();
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
exprt instantiate(
  const string_constraintt &axiom,
  const exprt &str,
  const exprt &val)
{
  exprt::operandst conjuncts;
  for(const auto &index : find_indexes(axiom.body, str, axiom.univ_var))
  {
    const exprt univ_var_value =
      linear_functiont::solve(linear_functiont{index}, axiom.univ_var, val);
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
