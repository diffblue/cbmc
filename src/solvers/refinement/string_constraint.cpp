/*******************************************************************\

 Module: String solver

 Author: Diffblue Ltd.

\*******************************************************************/

#include "string_constraint.h"

#include <solvers/sat/satcheck.h>
#include <util/symbol_table.h>

/// Runs a solver instance to verify whether an expression can only be
//  non-negative.
/// \param expr: the expression to check for negativity
/// \return true if `expr < 0` is unsatisfiable, false otherwise
static bool cannot_be_neg(const exprt &expr)
{
  satcheck_no_simplifiert sat_check;
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  boolbvt solver(ns, sat_check);
  const exprt zero = from_integer(0, expr.type());
  const binary_relation_exprt non_neg(expr, ID_lt, zero);
  solver << non_neg;
  return solver() == decision_proceduret::resultt::D_UNSATISFIABLE;
}

string_constraintt::string_constraintt(
  const symbol_exprt &_univ_var,
  const exprt &lower_bound,
  const exprt &upper_bound,
  const exprt &body)
  : univ_var(_univ_var),
    lower_bound(lower_bound),
    upper_bound(upper_bound),
    body(body)
{
  INVARIANT(
    cannot_be_neg(lower_bound),
    "String constraints must have non-negative lower bound.\n" +
      lower_bound.pretty());
  INVARIANT(
    cannot_be_neg(upper_bound),
    "String constraints must have non-negative upper bound.\n" +
      upper_bound.pretty());
}

/// Used for debug printing.
/// \param [in] expr: constraint to render
/// \return rendered string
std::string to_string(const string_not_contains_constraintt &expr)
{
  std::ostringstream out;
  out << "forall x in [" << format(expr.univ_lower_bound) << ", "
      << format(expr.univ_upper_bound) << "). " << format(expr.premise)
      << " => ("
      << "exists y in [" << format(expr.exists_lower_bound) << ", "
      << format(expr.exists_upper_bound) << "). " << format(expr.s0)
      << "[x+y] != " << format(expr.s1) << "[y])";
  return out.str();
}

void replace(
  const union_find_replacet &replace_map,
  string_not_contains_constraintt &constraint)
{
  replace_map.replace_expr(constraint.univ_lower_bound);
  replace_map.replace_expr(constraint.univ_upper_bound);
  replace_map.replace_expr(constraint.premise);
  replace_map.replace_expr(constraint.exists_lower_bound);
  replace_map.replace_expr(constraint.exists_upper_bound);
  replace_map.replace_expr(constraint.s0);
  replace_map.replace_expr(constraint.s1);
}

bool operator==(
  const string_not_contains_constraintt &left,
  const string_not_contains_constraintt &right)
{
  return left.univ_upper_bound == right.univ_upper_bound &&
         left.univ_lower_bound == right.univ_lower_bound &&
         left.exists_lower_bound == right.exists_lower_bound &&
         left.exists_upper_bound == right.exists_upper_bound &&
         left.premise == right.premise && left.s0 == right.s0 &&
         left.s1 == right.s1;
}
