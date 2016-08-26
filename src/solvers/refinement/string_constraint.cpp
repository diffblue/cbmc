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

string_constraintt string_constraintt::forall(symbol_exprt univ, exprt bound_inf, exprt bound_sup)
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
				 exprt exists_bound_sup, exprt s1, exprt s2)
{ 
  string_constraintt sc(premise);
  sc.form = NOT_CONTAINS;
  sc.bounds.push_back(univ_bound_inf);
  sc.bounds.push_back(univ_bound_inf);
  sc.bounds.push_back(univ_bound_sup);
  sc.bounds.push_back(exists_bound_inf);
  sc.bounds.push_back(exists_bound_sup);
  sc.compared_strings.push_back(s1);
  sc.compared_strings.push_back(s2);
  return sc;
}

