/** -*- C++ -*- *****************************************************\

Module: String expressions for PASS algorithm
        (see the PASS paper at HVC'13)

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_SOLVER_STRING_EXPR_H
#define CPROVER_SOLVER_STRING_EXPR_H

#include <langapi/language_ui.h>

#include <solvers/refinement/bv_refinement.h>
#include <solvers/refinement/string_constraint.h>
#include <solvers/refinement/string_functions.h>
#include <solvers/refinement/refined_string_type.h>


typedef std::vector<string_constraintt> axiom_vect;

// Expressions that encode strings
class string_exprt : public struct_exprt {
public:

  // Initialize string from the type of characters
  string_exprt(unsignedbv_typet char_type);

  // Default uses C character type
  string_exprt() : string_exprt(refined_string_typet::char_type()) {};

  // Add to the list of axioms, lemmas which should hold for the string to be 
  // equal to the given expression.
  static string_exprt of_expr(const exprt & unrefined_string, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);

  // We maintain a map from symbols to strings. If a symbol is not yet present we will create a new one with the correct type depending on whether this is a java or c string
  static string_exprt get_string_of_symbol(std::map<irep_idt, string_exprt> & symbol_to_string, const symbol_exprt & sym);

  // Generate a new symbol of the given type tp with a prefix 
  static symbol_exprt fresh_symbol(const irep_idt &prefix,
				   const typet &tp=bool_typet());

  // Expression corresponding to the length of the string
  inline const exprt & length() const { return op0();};

  // Expression corresponding to the content (array of characters) of the string
  inline const exprt & content() const { return op1();};

  static exprt within_bounds(const exprt & idx, const exprt & bound);

  // Expression of the character at position idx in the string
  inline index_exprt operator[] (const exprt & idx) const 
  { return index_exprt(content(), idx);}

  // Comparison on the length of the strings
  inline binary_relation_exprt operator> (const string_exprt & rhs) const 
  { return binary_relation_exprt(rhs.length(), ID_lt, length()); }
  inline binary_relation_exprt operator<= (const string_exprt & rhs) const 
  { return binary_relation_exprt(length(), ID_le, rhs.length()); }
  inline binary_relation_exprt operator>= (const string_exprt & rhs) const 
  { return binary_relation_exprt(length(), ID_ge, rhs.length()); }
  inline binary_relation_exprt operator> (const exprt & rhs) const 
  { return binary_relation_exprt(rhs, ID_lt, length()); }
  inline binary_relation_exprt operator>= (const exprt & rhs) const 
  { return binary_relation_exprt(length(), ID_ge, rhs); }
  inline binary_relation_exprt operator<= (const exprt & rhs) const 
  { return binary_relation_exprt(length(), ID_le, rhs); }
  //this one is used by maps: inline binary_relation_exprt operator< (const string_exprt & rhs) const  { return binary_relation_exprt(length(), ID_lt, rhs.length()); }
  //   inline binary_relation_exprt operator< (const exprt & rhs) const  { return binary_relation_exprt(length(), ID_lt, rhs); }

  static irep_idt extract_java_string(const symbol_exprt & s);

  void of_string_constant(irep_idt sval, int char_width, unsignedbv_typet char_type, axiom_vect &axioms);

  static unsigned next_symbol_id;

  friend inline string_exprt &to_string_expr(exprt &expr);

};


extern inline string_exprt &to_string_expr(exprt &expr){
  assert(expr.id()==ID_struct);
  return static_cast<string_exprt &>(expr);
}


#endif
