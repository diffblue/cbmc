/** -*- C++ -*- *****************************************************\

Module: String constraints
        (see the PASS paper at HVC'13

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_H

#include <langapi/language_ui.h>
#include <solvers/refinement/bv_refinement.h>
#include <solvers/refinement/refined_string_type.h>

class string_constraintt: public exprt
{
public:
  // String constraints are of the form
  // forall univ_var in [0,bound[. premise => body
  // or premise => body

  inline const exprt &premise() const
  {
    return op0();
  }

  inline const exprt &body() const
  {
    return op1();
  }

  inline const exprt &univ_var() const
  {
    return op2();
  }

  inline const exprt &upper_bound() const
  {
    return op3();
  }

  inline const exprt &lower_bound() const
  {
    return operands()[4];
  }

  // Trivial constraint
  string_constraintt() : exprt(ID_string_constraint)
  {
    assert(false); // string constraints should not be initialized directly
    copy_to_operands(true_exprt(), true_exprt());
  }

  // Returns a new constraints with an universal quantifier added
  string_constraintt(
    const symbol_exprt &univ,
    const exprt &bound_inf,
    const exprt &bound_sup,
    const exprt &prem,
    const exprt &body)
    : exprt(ID_string_constraint)
  {
    copy_to_operands(prem, body);
    copy_to_operands(univ, bound_sup, bound_inf);
  };

  // Default bound inferior is 0
  string_constraintt(
    const symbol_exprt &univ,
    const exprt &bound_sup,
    const exprt &prem,
    const exprt &body)
    : string_constraintt(univ, refined_string_typet::index_zero(),
                         bound_sup, prem, body)
  {};

  // Default premise is true
  string_constraintt
  (const symbol_exprt &univ, const exprt &bound_sup, const exprt &body)
    : string_constraintt
      (univ, refined_string_typet::index_zero(), bound_sup, true_exprt(), body)
  {};

  bool is_simple() const { return (operands().size()==2); }
  bool is_univ_quant() const { return (operands().size()==5); }
  bool is_not_contains() const { return false; }

  inline symbol_exprt get_univ_var() const
  { return to_symbol_expr(univ_var()); }

  inline exprt univ_within_bounds() const
  {
    return and_exprt
      (binary_relation_exprt(lower_bound(), ID_le, get_univ_var()),
       binary_relation_exprt(upper_bound(), ID_gt, get_univ_var()));
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
  // forall x in [lb,ub[. p(x) => exists y in [lb,ub[. s1[x+y] != s2[y]

  string_not_contains_constraintt(
    exprt univ_lower_bound,
    exprt univ_bound_sup,
    exprt premise,
    exprt exists_bound_inf,
    exprt exists_bound_sup,
    exprt s0,
    exprt s1)
    :exprt(ID_string_not_contains_constraint)
  {
    copy_to_operands(univ_lower_bound, univ_bound_sup, premise);
    copy_to_operands(exists_bound_inf, exists_bound_sup, s0);
    copy_to_operands(s1);
  };

  bool is_not_contains() const { return true; }

  inline const exprt &univ_lower_bound() const
  {
    return operands()[0];
  }

  inline const exprt &univ_upper_bound() const
  {
    return operands()[1];
  }

  inline const exprt &premise() const
  {
    return operands()[2];
  }

  inline const exprt &exists_lower_bound() const
  {
    return operands()[3];
  }

  inline const exprt &exists_upper_bound() const
  {
    return operands()[4];
  }

  inline const exprt &s0() const
  {
    return operands()[5];
  }

  inline const exprt &s1() const
  {
    return operands()[6];
  }
};

extern inline const string_not_contains_constraintt
&to_string_not_contains_constraint(const exprt &expr)
{
  assert(expr.id()==ID_string_not_contains_constraint
         && expr.operands().size()==7);
  return static_cast<const string_not_contains_constraintt &>(expr);
}

extern inline string_not_contains_constraintt
&to_string_not_contains_constraint(exprt &expr)
{
  assert(expr.id()==ID_string_not_contains_constraint
         && expr.operands().size()==7);
  return static_cast<string_not_contains_constraintt &>(expr);
}

#endif
