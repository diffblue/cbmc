/** -*- C++ -*- *****************************************************\

Module: String constraints
        (see the PASS paper at HVC'13)

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_SOLVER_STRING_CONSTRAINT_H
#define CPROVER_SOLVER_STRING_CONSTRAINT_H

#include <langapi/language_ui.h>
#include <solvers/refinement/bv_refinement.h>

class string_constraintt : public exprt 
{
private:
  // String axioms can have 3 different forms:
  // either a simple expression p, 
  // or universally quantified expression: forall x in [lb,ub[. p(x)
  // or a expression for non containment:
  // forall x in [lb,ub[. p(x) => exists y in [lb,ub[. s1[x+y] != s2[x]
  enum {SIMPLE, UNIV_QUANT, NOT_CONTAINS} form;

  // Universally quantified symbol
  symbol_exprt quantified_variable;
  // Bounds on the quantified variables (alternate between inf and sup)
  std::vector<exprt> bounds;
  // Only for NOT_CONTAINS constraints (represent s1 and s2)
  std::vector<exprt> compared_strings;

public:
  // True axiom
  string_constraintt() : exprt(true_exprt()) { form = SIMPLE; }

  // Axiom with no quantification, and no premise
  string_constraintt(exprt bod) : exprt(bod) { form = SIMPLE; }

  // Axiom with no quantification: prem => bod
  string_constraintt(exprt prem, exprt bod)  : exprt(implies_exprt(prem,bod))
  { form = SIMPLE; }

  // Add an universal quantifier, assume the premise are empty
  string_constraintt forall(symbol_exprt univ, exprt bound_inf, exprt bound_sup);
  
  static string_constraintt not_contains
  (exprt univ_lower_bound, exprt univ_bound_sup, exprt premise, 
   exprt exists_bound_inf, exprt exists_bound_sup, exprt s1, exprt s2);

  bool is_simple() const { return (form == SIMPLE); };
  bool is_univ_quant() const { return (form == UNIV_QUANT); };
  bool is_not_contains() const { return (form == NOT_CONTAINS); };
  
  exprt premise() const;

  exprt body() const;

  inline symbol_exprt get_univ_var() const { assert(form==UNIV_QUANT); return quantified_variable;}
  inline exprt univ_bound_inf() const { return bounds[0]; }
  inline exprt univ_bound_sup() const { return bounds[1]; }
  inline exprt exists_bound_inf() const { return bounds[2]; }
  inline exprt exists_bound_sup() const { return bounds[3]; }

 // Warning: this assumes a simple form
 inline string_constraintt operator&&(const exprt & a) {
   assert(form == SIMPLE);
   return string_constraintt(and_exprt(*this, a));
 }

 inline string_constraintt operator||(const exprt & a) {
   assert(form == SIMPLE);
   return string_constraintt(or_exprt(*this, a));
 }

 inline string_constraintt operator!() {
   assert(form == SIMPLE);
   return string_constraintt(not_exprt(*this));
 }
 

};


#endif
