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

private:
  // Auxiliary functions for of_expr
  void of_function_application(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);
  void of_string_literal(const function_application_exprt &f,axiom_vect &axioms);
  void of_string_concat(const string_exprt & s1, const string_exprt & s2, axiom_vect & axioms);
  void of_string_concat(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_concat_int(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_concat_long(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_concat_bool(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_concat_char(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_concat_double(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_concat_float(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_concat_code_point(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);

  // insert s2 in s1 at the given position
  void of_string_insert(const string_exprt & s1, const string_exprt & s2, const exprt &offset, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);
  void of_string_insert(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_insert_int(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_insert_long(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_insert_bool(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_insert_char(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_insert_double(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_insert_float(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);

  void of_string_substring(const string_exprt & str, const exprt & start, const exprt & end, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);
  void of_string_substring(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_trim(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_to_lower_case(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_to_upper_case(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_char_set(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_delete (const string_exprt &str, const exprt & start, const exprt & end, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);
  void of_string_delete(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_delete_char_at(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  void of_string_replace(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);

  // Warning: not working correctly at the moment
  void of_string_value_of(const function_application_exprt &f, axiom_vect &axioms);
  void of_string_set_length(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);
  void of_string_copy(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);
  void of_string_format(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);

  void of_empty_string(const function_application_exprt &f, axiom_vect & axioms);

  void of_int(const function_application_exprt &f, axiom_vect & axioms);
  void of_int(const exprt &i, axiom_vect & axioms, bool is_c_string, int max_size);
  void of_int_hex(const exprt &i, axiom_vect & axioms, bool is_c_string);
  void of_int_hex(const function_application_exprt &f,axiom_vect & axioms);
  void of_long(const function_application_exprt &f, axiom_vect & axioms);
  void of_long(const exprt &i, axiom_vect & axioms, bool is_c_string, int max_size);
  void of_bool(const function_application_exprt &f, axiom_vect & axioms);
  void of_bool(const exprt &i, axiom_vect & axioms, bool is_c_string);
  void of_char(const function_application_exprt &f, axiom_vect & axioms);
  void of_char(const exprt &i, axiom_vect & axioms, bool is_c_string);

  // Warning: the specifications of these functions is only partial:
  void of_float(const function_application_exprt &f, axiom_vect & axioms);
  void of_float(const exprt &f, axiom_vect & axioms, bool is_c_string, bool double_precision=false);
  void of_double(const function_application_exprt &f, axiom_vect & axioms);

  void of_code_point(const exprt &code_point, axiom_vect & axioms, bool is_c_string);
  void of_java_char_array(const exprt & char_array, axiom_vect & axioms);

  void of_if(const if_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect & axioms);

  static unsigned next_symbol_id;

  friend inline string_exprt &to_string_expr(exprt &expr);

};


extern inline string_exprt &to_string_expr(exprt &expr){
  assert(expr.id()==ID_struct);
  return static_cast<string_exprt &>(expr);
}


#endif
