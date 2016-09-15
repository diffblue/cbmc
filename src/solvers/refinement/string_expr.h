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

#define INDEX_WIDTH 32
#define CHAR_WIDTH 8
#define JAVA_CHAR_WIDTH 16


// Internal type used for strings
class string_ref_typet : public struct_typet {
public:
  // default is with C type of characters
  string_ref_typet();
  string_ref_typet(unsignedbv_typet char_type);

  // Type for the content (list of characters) of a string
  inline array_typet get_content_type() 
  { return to_array_type((to_struct_type(*this)).components()[1].type());}

  // Types used in this refinement
  static inline unsignedbv_typet char_type() { return unsignedbv_typet(CHAR_WIDTH);}

  static inline unsignedbv_typet java_char_type() { return unsignedbv_typet(JAVA_CHAR_WIDTH);}

  //unsignedbv_typet index_type(INDEX_WIDTH);
  static inline signedbv_typet index_type() { return signedbv_typet(INDEX_WIDTH);}

  static inline exprt index_zero() { return constant_exprt(integer2binary(0, INDEX_WIDTH), index_type());}

  // For C the unrefined string type is __CPROVER_string, for java it is a 
  // pointer to a strict with tag java.lang.String

  static bool is_c_string_type(const typet & type);
  static bool is_java_string_type(const typet & type);
  static bool is_java_string_builder_type(const typet & type);
  static inline bool is_unrefined_string_type(const typet & type)
  {  return (is_c_string_type(type) || is_java_string_type(type) || is_java_string_builder_type(type)); }
  static inline bool is_unrefined_string(const exprt & expr)
  {  return (is_unrefined_string_type(expr.type())); }

  static inline constant_exprt index_of_int(int i) {
    return constant_exprt(integer2binary(i, INDEX_WIDTH), index_type());
  }

};

typedef std::vector<string_constraintt> axiom_vect;

// Expressions that encode strings
class string_exprt : public struct_exprt {
public:
  string_exprt();
  string_exprt(unsignedbv_typet char_type);


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

  static irep_idt extract_java_string(const symbol_exprt & s);

  void of_string_constant(irep_idt sval, int char_width, unsignedbv_typet char_type, axiom_vect &axioms);

private:
  // Auxiliary functions for of_expr
  void of_function_application(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);
  void of_string_literal(const function_application_exprt &f,axiom_vect &axioms);
  void of_string_concat(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_substring(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_char_set(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_copy(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);
  void of_empty_string(const function_application_exprt &f, axiom_vect & axioms);
  void of_int(const function_application_exprt &f, axiom_vect & axioms);
  void of_long(const function_application_exprt &f, axiom_vect & axioms);
  void of_int(const exprt &i, axiom_vect & axioms, bool is_c_string, int max_size);

  void of_if(const if_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);

  void of_struct(const struct_exprt & expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);

  static unsigned next_symbol_id;

  friend inline string_exprt &to_string_expr(exprt &expr);

public:
  exprt convert_string_equal(const function_application_exprt &f, axiom_vect & axioms);
};


extern inline string_exprt &to_string_expr(exprt &expr){
  assert(expr.id()==ID_struct);
  return static_cast<string_exprt &>(expr);
}


#endif
