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
  // String axioms can have 4 different forms:
  // either a simple expression p, 
  // or a string constant: forall x in [0,|s|[. s(x) = c(x)
  // or universally quantified expression: forall x in [lb,ub[. p(x)
  // or a expression for non containment:
  // forall x in [lb,ub[. p(x) => exists y in [lb,ub[. s1[x+y] != s2[y]
  enum {SIMPLE, STRING_CONSTANT, UNIV_QUANT, NOT_CONTAINS} form;

  // Universally quantified symbol
  symbol_exprt quantified_variable;
  // Bounds on the quantified variables (alternate between inf and sup)
  std::vector<exprt> bounds;
  // Only for NOT_CONTAINS constraints (represent s1 and s2)
  std::vector<exprt> compared_strings;

public:

// used to store information about witnesses for not_contains constraints
  symbol_exprt witness;


  // True axiom
  string_constraintt() : exprt(true_exprt()) { form = SIMPLE; }

  // Axiom with no quantification, and no premise
  string_constraintt(exprt bod, bool is_string_constant=false) : exprt(bod) { form = is_string_constant?SIMPLE:STRING_CONSTANT; }

  // Axiom with no quantification: prem => bod
  string_constraintt(exprt prem, exprt bod)  : exprt(implies_exprt(prem,bod))
  { form = SIMPLE; }

  // Add an universal quantifier
  string_constraintt forall(const symbol_exprt & univ, const exprt & bound_inf, const exprt & bound_sup);

  // Bound a variable that is existentially quantified
  string_constraintt exists(const symbol_exprt & exist, const exprt & bound_inf, const exprt & bound_sup);
  
  static string_constraintt not_contains
  (exprt univ_lower_bound, exprt univ_bound_sup, exprt premise, 
   exprt exists_bound_inf, exprt exists_bound_sup, exprt s0, exprt s1);

  bool is_simple() const { return (form == SIMPLE); };
  bool is_string_constant() const { return (form == STRING_CONSTANT); };
  bool is_univ_quant() const { return (form == UNIV_QUANT); };
  bool is_not_contains() const { return (form == NOT_CONTAINS); };
  
  exprt premise() const;

  exprt body() const;

  inline exprt s0() const { assert(is_not_contains()); return compared_strings[0];}
  inline exprt s1() const { assert(is_not_contains()); return compared_strings[1];}


  inline symbol_exprt get_univ_var() const { assert(form==UNIV_QUANT); return quantified_variable;}
  inline exprt univ_bound_inf() const { return bounds[0]; }
  inline exprt univ_bound_sup() const { return bounds[1]; }
  inline exprt univ_within_bounds() const 
  { return and_exprt(binary_relation_exprt(bounds[0],ID_le,get_univ_var()),
		     binary_relation_exprt(bounds[1],ID_gt,get_univ_var())); }
  inline exprt exists_bound_inf() const { return bounds[2]; }
  inline exprt exists_bound_sup() const { return bounds[3]; }

  inline exprt witness_of(const exprt & univ_val) const { return index_exprt(witness, univ_val); }


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
