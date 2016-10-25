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
  constant_exprt constant_unsigned(int i,size_t width); 
  constant_exprt constant_signed(int i,size_t width); 
  unsignedbv_typet get_char_type();
  size_t get_char_width(); 
  inline signedbv_typet get_index_type() {return refined_string_typet::index_type();};

  std::vector<string_constraintt> axioms;

  // Create a new string expression and add the necessary lemma
  // to ensure its equal to the given string expression.
  string_exprt make_string(const exprt &str);

  // Same thing but associates the string to the given symbol instead 
  // of returning it.
  void make_string(const symbol_exprt & sym, const exprt &str);


  // Boolean symbols that are used to know whether the results 
  // of some functions should be true.
  std::vector<symbol_exprt> boolean_symbols;

  // Symbols used in existential quantifications
  std::vector<symbol_exprt> index_symbols;

  symbol_exprt fresh_exist_index(const irep_idt &prefix);
  symbol_exprt fresh_univ_index(const irep_idt &prefix);
  symbol_exprt fresh_boolean(const irep_idt &prefix);

  std::map<irep_idt, string_exprt> symbol_to_string;
  inline void assign_to_symbol(const symbol_exprt & sym, const string_exprt & expr)
  { symbol_to_string[sym.get_identifier()]= expr; }  

  // We maintain a map from symbols to strings. If a symbol is not yet present we will create a new one with the correct type depending on whether this is a java or c string
  string_exprt get_string_of_symbol(const symbol_exprt & sym);

  // Add to the list of axioms, lemmas which should hold for the string to be 
  // equal to the given expression.
  string_exprt of_expr(const exprt & unrefined_string);

  string_exprt string_of_expr(const exprt & expr);
  void string_of_expr(const symbol_exprt & sym, const exprt & str);
  string_exprt string_of_symbol(const symbol_exprt & sym);

  // The following functions convert different string functions 
  // and add the corresponding lemmas to a list of properties to be checked  
  exprt function_application(const function_application_exprt &expr);

  string_exprt empty_string(const function_application_exprt &f);
  string_exprt string_char_set(const function_application_exprt &expr);
  exprt string_char_at(const function_application_exprt &f);
  exprt string_code_point_at(const function_application_exprt &f);
  exprt string_code_point_before(const function_application_exprt &f);
  string_exprt string_copy(const function_application_exprt &f);
  string_exprt string_concat(const string_exprt & s1, const string_exprt & s2);
  string_exprt string_concat(const function_application_exprt &f);
  string_exprt string_concat_int(const function_application_exprt &f);
  string_exprt string_concat_long(const function_application_exprt &f);
  string_exprt string_concat_bool(const function_application_exprt &f);
  string_exprt string_concat_char(const function_application_exprt &f);
  string_exprt string_concat_double(const function_application_exprt &f);
  string_exprt string_concat_float(const function_application_exprt &f);
  string_exprt string_concat_code_point(const function_application_exprt &f);
  string_exprt string_constant(irep_idt sval, int char_width, unsignedbv_typet char_type);
  exprt string_contains(const function_application_exprt &f);
  exprt string_equal(const function_application_exprt &f);
  exprt string_equals_ignore_case(const function_application_exprt &f);
  exprt string_data(const function_application_exprt &f);
  string_exprt string_delete (const string_exprt &str, const exprt & start, const exprt & end);
  string_exprt string_delete(const function_application_exprt &expr);
  string_exprt string_delete_char_at(const function_application_exprt &expr);
  string_exprt string_format(const function_application_exprt &f);
  exprt string_hash_code(const function_application_exprt &f);

  // Warning: the specifications are only partial for some of the "index_of" functions
  exprt string_index_of(const string_exprt &str, const exprt & c, const exprt & from_index);
  exprt string_index_of_string(const string_exprt &str, const string_exprt & substring, const exprt & from_index);
  exprt string_index_of(const function_application_exprt &f);
  exprt string_last_index_of_string(const string_exprt &str, const string_exprt & substring, const exprt & from_index);
  exprt string_last_index_of(const string_exprt &str, const exprt & c, const exprt & from_index);
  exprt string_last_index_of(const function_application_exprt &f);

  string_exprt string_insert(const string_exprt & s1, const string_exprt & s2, const exprt &offset);
  string_exprt string_insert(const function_application_exprt &f);
  string_exprt string_insert_int(const function_application_exprt &f);
  string_exprt string_insert_long(const function_application_exprt &f);
  string_exprt string_insert_bool(const function_application_exprt &f);
  string_exprt string_insert_char(const function_application_exprt &f);
  string_exprt string_insert_double(const function_application_exprt &f);
  string_exprt string_insert_float(const function_application_exprt &f);
  exprt string_is_empty(const function_application_exprt &f);
  exprt string_is_prefix(const string_exprt &prefix, const string_exprt &str, const exprt & offset);
  exprt string_is_prefix(const function_application_exprt &f, bool swap_arguments=false);
  exprt string_is_suffix(const function_application_exprt &f, bool swap_arguments=false);
  exprt string_length(const function_application_exprt &f);
  string_exprt string_literal(const function_application_exprt &f);
  string_exprt of_int(const function_application_exprt &f);
  string_exprt of_int(const exprt &i, size_t max_size);
  string_exprt of_int_hex(const exprt &i);
  string_exprt of_int_hex(const function_application_exprt &f);
  string_exprt of_long(const function_application_exprt &f);
  string_exprt of_long(const exprt &i, size_t max_size);
  string_exprt of_bool(const function_application_exprt &f);
  string_exprt of_bool(const exprt &i);
  string_exprt of_char(const function_application_exprt &f);
  string_exprt of_char(const exprt &i);

  // Warning: the specifications of these functions is only partial:
  string_exprt of_float(const function_application_exprt &f);
  string_exprt of_float(const exprt &f, bool double_precision=false);
  string_exprt of_double(const function_application_exprt &f);

  string_exprt string_replace(const function_application_exprt &f);
  string_exprt string_set_length(const function_application_exprt &f);

  // Warning: the specification may not be correct for the case where the string is not long enough
  string_exprt string_substring(const string_exprt & str, const exprt & start, const exprt & end);
  string_exprt string_substring(const function_application_exprt &expr);

  string_exprt string_to_lower_case(const function_application_exprt &expr);
  string_exprt string_to_upper_case(const function_application_exprt &expr);
  string_exprt string_trim(const function_application_exprt &expr);

  // Warning: not working correctly at the moment
  string_exprt string_value_of(const function_application_exprt &f);

  string_exprt code_point(const exprt &code_point);
  string_exprt java_char_array(const exprt & char_array);

  string_exprt string_if(const if_exprt &expr);

  exprt char_literal(const function_application_exprt &f);

  
  // Warning: this function is underspecified
  exprt string_code_point_count(const function_application_exprt &f);
  // Warning: this function is underspecified
  exprt string_offset_by_code_point(const function_application_exprt &f);
  exprt string_parse_int(const function_application_exprt &f);
  exprt string_to_char_array(const function_application_exprt &f);

  exprt string_compare_to(const function_application_exprt &f);

  // Warning: this does not work at the moment because of the way we treat string pointers
  symbol_exprt string_intern(const function_application_exprt &f);

  // Check that the given string is from the right language
  void check_char_type(const exprt & str);

private:

  enum {C, JAVA, UNKNOWN} language;

  
  inline bool use_c_string() {return (language == C);}

  // assert that the number of argument is equal to nb and extract them
  inline function_application_exprt::argumentst args(const function_application_exprt &expr, size_t nb)
  {
    function_application_exprt::argumentst args = expr.arguments();
    assert(args.size() == nb);
    return args;
  }

  exprt int_of_hex_char(exprt chr, unsigned char_width, typet char_type);
  exprt is_high_surrogate(const exprt & chr);
  exprt is_low_surrogate(const exprt & chr);
  std::map<string_exprt, symbol_exprt> pool;
  std::map<string_exprt, symbol_exprt> hash;

};

#endif
