#include "string_constraint.h"

void replace(string_constraintt &axiom, const replace_mapt& symbol_resolve)
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

std::string from_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const string_constraintt &expr)
{
  return "forall "+from_expr(ns, identifier, expr.univ_var)+" in ["+
    from_expr(ns, identifier, expr.lower_bound)+", "+
    from_expr(ns, identifier, expr.upper_bound)+"). "+
    from_expr(ns, identifier, expr.premise)+" => "+
    from_expr(ns, identifier, expr.body);
}

std::string from_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const string_not_contains_constraintt &expr)
{
  return "forall x in ["+
    from_expr(ns, identifier, expr.univ_lower_bound())+", "+
    from_expr(ns, identifier, expr.univ_upper_bound())+"). "+
    from_expr(ns, identifier, expr.premise())+" => ("+
    "exists y in ["+from_expr(ns, identifier, expr.exists_lower_bound())+", "+
    from_expr(ns, identifier, expr.exists_upper_bound())+"). "+
    from_expr(ns, identifier, expr.s0())+"[x+y] != "+
    from_expr(ns, identifier, expr.s1())+"[y])";
}

const string_not_contains_constraintt
&to_string_not_contains_constraint(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_string_not_contains_constraint);
  DATA_INVARIANT(
    expr.operands().size()==7,
    string_refinement_invariantt("string_not_contains_constraintt must have 7 "
      "operands"));
  return static_cast<const string_not_contains_constraintt &>(expr);
}

string_not_contains_constraintt
&to_string_not_contains_constraint(exprt &expr)
{
  PRECONDITION(expr.id()==ID_string_not_contains_constraint);
  DATA_INVARIANT(
    expr.operands().size()==7,
    string_refinement_invariantt("string_not_contains_constraintt must have 7 "
      "operands"));
  return static_cast<string_not_contains_constraintt &>(expr);
}
