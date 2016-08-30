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

#define INDEX_WIDTH 32
#define CHAR_WIDTH 8


// Internal type used for strings
class string_ref_typet : public struct_typet {
public:
  string_ref_typet();

  // Type for the content (list of characters) of a string
  inline array_typet get_content_type() 
  { return to_array_type((to_struct_type(*this)).components()[1].type());}

  // Types used in this refinement
  static inline unsignedbv_typet char_type() { return unsignedbv_typet(CHAR_WIDTH);}
  //unsignedbv_typet index_type(INDEX_WIDTH);
  static inline signedbv_typet index_type() { return signedbv_typet(INDEX_WIDTH);}

  static inline exprt index_zero() { return constant_exprt(integer2binary(0, INDEX_WIDTH), index_type());}

  static bool is_unrefined_string_type(const typet & type);
};

typedef std::vector<string_constraintt> axiom_vect;

// Expressions that encode strings
class string_exprt : public struct_exprt {
public:
  string_exprt();


  // Add to the list of axioms, lemmas which should hold for the string to be 
  // equal to the given expression.
  static string_exprt of_expr(const exprt & unrefined_string, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);

  // Generate a new symbol of the given type tp with a prefix 
  static symbol_exprt fresh_symbol(const irep_idt &prefix,
				   const typet &tp=bool_typet());
  

  // Expression corresponding to the length of the string
  inline const exprt & length() const { return op0();};
  // Expression corresponding to the content (array of characters) of the string
  inline const exprt & content() const { return op1();};

  static exprt within_bounds(const exprt & idx, const exprt & bound);

  // Expression of the character at position idx in the string
  inline index_exprt operator[] (exprt idx)
  { return index_exprt(content(), idx);}

  // Comparison on the length of the strings
  inline binary_relation_exprt operator< (string_exprt rhs)
  { return binary_relation_exprt(length(), ID_lt, rhs.length()); }
  inline binary_relation_exprt operator> (string_exprt rhs)
  { return binary_relation_exprt(rhs.length(), ID_lt, length()); }
  inline binary_relation_exprt operator<= (string_exprt rhs)
  { return binary_relation_exprt(length(), ID_le, rhs.length()); }
  inline binary_relation_exprt operator>= (string_exprt rhs)
  { return binary_relation_exprt(length(), ID_ge, rhs.length()); }
  inline binary_relation_exprt operator< (const exprt & rhs)
  { return binary_relation_exprt(length(), ID_lt, rhs); }
  inline binary_relation_exprt operator> (const exprt & rhs)
  { return binary_relation_exprt(rhs, ID_lt, length()); }
  inline binary_relation_exprt operator>= (const exprt & rhs)
  { return binary_relation_exprt(length(), ID_ge, rhs); }
  inline binary_relation_exprt operator<= (const exprt & rhs)
  { return binary_relation_exprt(length(), ID_le, rhs); }

private:
  // Auxiliary functions for of_expr
  void of_function_application(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);

  void of_string_literal(const function_application_exprt &f,axiom_vect &axioms);
  void of_string_concat(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_substring(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_char_set(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);

  void of_if(const if_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);

  static unsigned next_symbol_id;

  friend inline string_exprt &to_string_expr(exprt &expr);
  
};


extern inline string_exprt &to_string_expr(exprt &expr){
  assert(expr.id()==ID_struct);
  return static_cast<string_exprt &>(expr);
}

// The following functions convert different string functions to 
// bit vectors and add the corresponding lemmas to a list of
// properties to be checked  
bvt convert_string_equal(const function_application_exprt &f);
bvt convert_string_copy(const function_application_exprt &f);
bvt convert_string_length(const function_application_exprt &f);
bvt convert_string_is_prefix(const function_application_exprt &f);
bvt convert_string_is_suffix(const function_application_exprt &f);
bvt convert_string_contains(const function_application_exprt &f);
bvt convert_string_index_of(const function_application_exprt &f);
bvt convert_string_last_index_of(const function_application_exprt &f);
bvt convert_char_literal(const function_application_exprt &f);
bvt convert_string_char_at(const function_application_exprt &f);




#endif
