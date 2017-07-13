/*******************************************************************\

Module: Defines string constraints. These are formulas talking about strings. 
        We implemented two forms of constraints: `string_constraintt` 
        are formulas of the form $\forall univ_var \in [lb,ub[. prem => body$,
        and not_contains_constraintt of the form:
        $\forall x in [lb,ub[. p(x) => \exists y in [lb,ub[. s1[x+y] != s2[y]$.

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Defines string constraints. These are formulas talking about strings.  We
///   implemented two forms of constraints: `string_constraintt`  are formulas
///   of the form $\forall univ_var \in [lb,ub[. prem => body$, and
///   not_contains_constraintt of the form: $\forall x in [lb,ub[. p(x) =>
///   \exists y in [lb,ub[. s1[x+y] != s2[y]$.

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_H

#include <langapi/language_ui.h>
#include <solvers/refinement/bv_refinement.h>
#include <util/refined_string_type.h>

class string_constraintt: public exprt
{
public:
  // String constraints are of the form
  // forall univ_var in [lower_bound,upper_bound[. premise => body

  const exprt &premise() const
  {
    return op0();
  }

  const exprt &body() const
  {
    return op1();
  }

  const symbol_exprt &univ_var() const
  {
    return to_symbol_expr(op2());
  }

  const exprt &upper_bound() const
  {
    return op3();
  }

  const exprt &lower_bound() const
  {
    return operands()[4];
  }

 private:
  string_constraintt();

 public:
  string_constraintt(
    const symbol_exprt &_univ_var,
    const exprt &bound_inf,
    const exprt &bound_sup,
    const exprt &prem,
    const exprt &body):
    exprt(ID_string_constraint)
  {
    copy_to_operands(prem, body);
    copy_to_operands(_univ_var, bound_sup, bound_inf);
  }

  // Default bound inferior is 0
  string_constraintt(
    const symbol_exprt &_univ_var,
    const exprt &bound_sup,
    const exprt &prem,
    const exprt &body):
    string_constraintt(
      _univ_var,
      from_integer(0, _univ_var.type()),
      bound_sup,
      prem,
      body)
  {}

  // Default premise is true
  string_constraintt(
    const symbol_exprt &_univ_var,
    const exprt &bound_sup,
    const exprt &body):
    string_constraintt(_univ_var, bound_sup, true_exprt(), body)
  {}

  exprt univ_within_bounds() const
  {
    return and_exprt(
      binary_relation_exprt(lower_bound(), ID_le, univ_var()),
      binary_relation_exprt(upper_bound(), ID_gt, univ_var()));
  }
};

extern inline const string_constraintt &to_string_constraint(const exprt &expr)
{
  assert(expr.id()==ID_string_constraint && expr.operands().size()==5);
  return static_cast<const string_constraintt &>(expr);
}

extern inline string_constraintt &to_string_constraint(exprt &expr)
{
  assert(expr.id()==ID_string_constraint && expr.operands().size()==5);
  return static_cast<string_constraintt &>(expr);
}

class string_not_contains_constraintt: public exprt
{
public:
  // string_not contains_constraintt are formula of the form:
  // forall x in [lb,ub[. p(x) => exists y in [lb,ub[. s0[x+y] != s1[y]

  string_not_contains_constraintt(
    exprt univ_lower_bound,
    exprt univ_bound_sup,
    exprt premise,
    exprt exists_bound_inf,
    exprt exists_bound_sup,
    const string_exprt &s0,
    const string_exprt &s1):
  exprt(ID_string_not_contains_constraint)
  {
    copy_to_operands(univ_lower_bound, univ_bound_sup, premise);
    copy_to_operands(exists_bound_inf, exists_bound_sup, s0);
    copy_to_operands(s1);
  };

  const exprt &univ_lower_bound() const
  {
    return op0();
  }

  const exprt &univ_upper_bound() const
  {
    return op1();
  }

  const exprt &premise() const
  {
    return op2();
  }

  const exprt &exists_lower_bound() const
  {
    return op3();
  }

  const exprt &exists_upper_bound() const
  {
    return operands()[4];
  }

  const string_exprt &s0() const
  {
    return to_string_expr(operands()[5]);
  }

  const string_exprt &s1() const
  {
    return to_string_expr(operands()[6]);
  }
};

inline const string_not_contains_constraintt
&to_string_not_contains_constraint(const exprt &expr)
{
  assert(expr.id()==ID_string_not_contains_constraint);
  assert(expr.operands().size()==7);
  return static_cast<const string_not_contains_constraintt &>(expr);
}

inline string_not_contains_constraintt
&to_string_not_contains_constraint(exprt &expr)
{
  assert(expr.id()==ID_string_not_contains_constraint);
  assert(expr.operands().size()==7);
  return static_cast<string_not_contains_constraintt &>(expr);
}

#endif
