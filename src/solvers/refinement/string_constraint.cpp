/** -*- C++ -*- *****************************************************\

Module: String constraints
        (see the PASS paper at HVC'13)

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_constraint.h>


exprt string_constraintt::premise() const {
  if(form == SIMPLE || form == UNIV_QUANT) {
    if(id() == ID_implies)
      return op0();
    else 
      return true_exprt();
  }
  else {
    return(*this);
  }
}

exprt string_constraintt::body() const {
  if(form == SIMPLE || form == UNIV_QUANT) {
    if(id() == ID_implies)
      return op1();
    else
      return(*this);
  } else throw "string_constraintt::body() should not be applied to NOT_CONTAINS expression";
}

string_constraintt string_constraintt::forall(const symbol_exprt & univ, const exprt & bound_inf, const exprt & bound_sup)
{
  string_constraintt sc(*this);
  sc.form = UNIV_QUANT;
  sc.quantified_variable = univ;
  sc.bounds.push_back(bound_inf);
  sc.bounds.push_back(bound_sup);
  return sc;
}

string_constraintt string_constraintt::not_contains(exprt univ_bound_inf, exprt univ_bound_sup, 
				 exprt premise, exprt exists_bound_inf, 
				 exprt exists_bound_sup, exprt s0, exprt s1)
{ 
  string_constraintt sc(premise);
  sc.form = NOT_CONTAINS;
  sc.bounds.push_back(univ_bound_inf);
  sc.bounds.push_back(univ_bound_inf);
  sc.bounds.push_back(univ_bound_sup);
  sc.bounds.push_back(exists_bound_inf);
  sc.bounds.push_back(exists_bound_sup);
  sc.compared_strings.push_back(s0);
  sc.compared_strings.push_back(s1);
  return sc;
}

string_constraintt string_constraintt::exists(const symbol_exprt & exist, const exprt & bound_inf, const exprt & bound_sup)
{
  assert(is_simple() || is_string_constant());
  return string_constraintt
    (and_exprt(*this, 
	       and_exprt(binary_relation_exprt(exist, ID_ge, bound_inf),
			 binary_relation_exprt(exist, ID_lt, bound_sup))));
}
