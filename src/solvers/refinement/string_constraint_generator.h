/** -*- C++ -*- *****************************************************\

Module: Constraint generation from string function calls
        for the PASS algorithm (see the PASS paper at HVC'13)

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_SOLVER_STRING_CONSTRAINT_GENERATOR_H
#define CPROVER_SOLVER_STRING_CONSTRAINT_GENERATOR_H

#include <solvers/refinement/string_expr.h>

class string_constraint_generatort {
public:

  string_constraint_generatort() : language(UNKNOWN){ }

  constant_exprt constant_char(int i); 
  inline unsignedbv_typet get_char_type() 
  { 
    return (language==UNKNOWN?refined_string_typet::char_type():refined_string_typet::java_char_type());
  }

  string_exprt string_of_expr(const exprt & expr);
  string_exprt of_function_application(const function_application_exprt &expr);
  string_exprt of_string_literal(const function_application_exprt &f,axiom_vect &axioms);
  string_exprt of_string_concat(const string_exprt & s1, const string_exprt & s2, axiom_vect & axioms);
  string_exprt of_string_concat(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_concat_int(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_concat_long(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_concat_bool(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_concat_char(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_concat_double(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_concat_float(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_concat_code_point(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);

  // insert s2 in s1 at the given position
  string_exprt of_string_insert(const string_exprt & s1, const string_exprt & s2, const exprt &offset);
  string_exprt of_string_insert(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_insert_int(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_insert_long(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_insert_bool(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_insert_char(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_insert_double(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_insert_float(const function_application_exprt &f, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);

  string_exprt of_string_substring(const string_exprt & str, const exprt & start, const exprt & end);
  string_exprt of_string_substring(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_trim(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_to_lower_case(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_to_upper_case(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_char_set(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_delete (const string_exprt &str, const exprt & start, const exprt & end);
  string_exprt of_string_delete(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_delete_char_at(const function_application_exprt &expr, std::map<irep_idt, string_exprt> & symbol_to_string, axiom_vect &axioms);
  string_exprt of_string_replace(const function_application_exprt &f);

  // Warning: not working correctly at the moment
  string_exprt of_string_value_of(const function_application_exprt &f, axiom_vect &axioms);
  string_exprt of_string_set_length(const function_application_exprt &f);
  string_exprt of_string_copy(const function_application_exprt &f);
  string_exprt of_string_format(const function_application_exprt &f);

  string_exprt of_empty_string(const function_application_exprt &f, axiom_vect & axioms);

  string_exprt of_int(const function_application_exprt &f, axiom_vect & axioms);
  string_exprt of_int(const exprt &i, axiom_vect & axioms, bool is_c_string, int max_size);
  string_exprt of_int_hex(const exprt &i, axiom_vect & axioms, bool is_c_string);
  string_exprt of_int_hex(const function_application_exprt &f,axiom_vect & axioms);
  string_exprt of_long(const function_application_exprt &f, axiom_vect & axioms);
  string_exprt of_long(const exprt &i, axiom_vect & axioms, bool is_c_string, int max_size);
  string_exprt of_bool(const function_application_exprt &f, axiom_vect & axioms);
  string_exprt of_bool(const exprt &i, axiom_vect & axioms, bool is_c_string);
  string_exprt of_char(const function_application_exprt &f, axiom_vect & axioms);
  string_exprt of_char(const exprt &i, axiom_vect & axioms, bool is_c_string);

  // Warning: the specifications of these functions is only partial:
  string_exprt of_float(const function_application_exprt &f, axiom_vect & axioms);
  string_exprt of_float(const exprt &f, axiom_vect & axioms, bool is_c_string, bool double_precision=false);
  string_exprt of_double(const function_application_exprt &f, axiom_vect & axioms);

  string_exprt of_code_point(const exprt &code_point, axiom_vect & axioms, bool is_c_string);
  string_exprt of_java_char_array(const exprt & char_array, axiom_vect & axioms);

  string_exprt of_if(const if_exprt &expr);

  // The following functions convert different string functions 
  // and add the corresponding lemmas to a list of properties to be checked  
  exprt convert_string_equal(const function_application_exprt &f);
  exprt convert_string_equals_ignore_case(const function_application_exprt &f);
  exprt convert_string_is_empty(const function_application_exprt &f);
  bvt convert_string_length(const function_application_exprt &f);
  exprt convert_string_is_prefix(const string_exprt &prefix, const string_exprt &str, const exprt & offset);
  exprt convert_string_is_prefix(const function_application_exprt &f, bool swap_arguments=false);
  bvt convert_string_is_suffix(const function_application_exprt &f, bool swap_arguments=false);
  bvt convert_string_contains(const function_application_exprt &f);
  exprt convert_string_hash_code(const function_application_exprt &f);
  exprt convert_string_index_of(const string_exprt &str, const exprt & c, const exprt & from_index);
  exprt convert_string_index_of_string(const string_exprt &str, const string_exprt & substring, const exprt & from_index);
  exprt convert_string_last_index_of_string(const string_exprt &str, const string_exprt & substring, const exprt & from_index);
  exprt convert_string_index_of(const function_application_exprt &f);
  exprt convert_string_last_index_of(const string_exprt &str, const exprt & c, const exprt & from_index);
  exprt convert_string_last_index_of(const function_application_exprt &f);
  bvt convert_char_literal(const function_application_exprt &f);
  bvt convert_string_char_at(const function_application_exprt &f);
  exprt convert_string_code_point_at(const function_application_exprt &f);
  exprt convert_string_code_point_before(const function_application_exprt &f);
  
  // Warning: this function is underspecified
  exprt convert_string_code_point_count(const function_application_exprt &f);
  // Warning: this function is underspecified
  exprt convert_string_offset_by_code_point(const function_application_exprt &f);
  exprt convert_string_parse_int(const function_application_exprt &f);
  exprt convert_string_to_char_array(const function_application_exprt &f);

  exprt convert_string_compare_to(const function_application_exprt &f);

  // Warning: this does not work at the moment because of the way we treat string pointers
  symbol_exprt convert_string_intern(const function_application_exprt &f);


private:

  enum {C, JAVA, UNKNOWN} language;

  // Check that the given string is from the right language
  void check_char_type(const exprt & str);
  
  std::vector<string_constraintt> axioms;
  // Boolean symbols that are used to know whether the results 
  // of some functions should be true.
  std::vector<symbol_exprt> boolean_symbols;

  // Symbols used in existential quantifications
  std::vector<symbol_exprt> index_symbols;

  std::map<irep_idt, string_exprt> symbol_to_string;
  inline void assign_to_symbol(const symbol_exprt & sym, const string_exprt & expr){
    symbol_to_string[sym.get_identifier()]= expr;
  }  

  string_exprt string_of_symbol(const symbol_exprt & sym);

};

#endif
