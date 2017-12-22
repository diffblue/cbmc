#include "string_constraint.h"

void replace(string_constraintt &axiom, const replace_mapt &symbol_resolve)
{
  replace_expr(symbol_resolve, axiom.premise);
  replace_expr(symbol_resolve, axiom.body);
  replace_expr(symbol_resolve, axiom.univ_var);
  replace_expr(symbol_resolve, axiom.upper_bound);
  replace_expr(symbol_resolve, axiom.lower_bound);
}

exprt univ_within_bounds(const string_constraintt &axiom)
{
  return and_exprt(
    binary_relation_exprt(axiom.lower_bound, ID_le, axiom.univ_var),
    binary_relation_exprt(axiom.upper_bound, ID_gt, axiom.univ_var));
}

std::string to_string(const string_constraintt &expr)
{
  std::ostringstream out;
  out << "forall " << format(expr.univ_var) << " in ["
      << format(expr.lower_bound) << ", " << format(expr.upper_bound) << "). "
      << format(expr.premise) << " => " << format(expr.body);
  return out.str();
}

std::string to_string(const string_not_contains_constraintt &expr)
{
  std::ostringstream out;
  out << "forall x in [" << format(expr.univ_lower_bound()) << ", "
      << format(expr.univ_upper_bound()) << "). " << format(expr.premise())
      << " => ("
      << "exists y in [" << format(expr.exists_lower_bound()) << ", "
      << format(expr.exists_upper_bound()) << "). " << format(expr.s0())
      << "[x+y] != " << format(expr.s1()) << "[y])";
  return out.str();
}

const string_not_contains_constraintt &
to_string_not_contains_constraint(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_string_not_contains_constraint);
  DATA_INVARIANT(
    expr.operands().size() == 7,
    string_refinement_invariantt(
      "string_not_contains_constraintt must have 7 "
      "operands"));
  return static_cast<const string_not_contains_constraintt &>(expr);
}

string_not_contains_constraintt &to_string_not_contains_constraint(exprt &expr)
{
  PRECONDITION(expr.id() == ID_string_not_contains_constraint);
  DATA_INVARIANT(
    expr.operands().size() == 7,
    string_refinement_invariantt(
      "string_not_contains_constraintt must have 7 "
      "operands"));
  return static_cast<string_not_contains_constraintt &>(expr);
}
