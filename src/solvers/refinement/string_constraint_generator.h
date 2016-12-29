/** -*- C++ -*- *****************************************************\

Module: Generates string constraints to link results from string functions
        with their arguments. This is inspired by the PASS paper at HVC'13
	which gives examples of constraints for several functions.

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_GENERATOR_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_GENERATOR_H

#include <solvers/refinement/string_expr.h>

class string_constraint_generatort
{
public:
  // This module keeps a list of axioms. It has methods which generate
  // string constraints for different string funcitons and add them
  // to the axiom list.

  string_constraint_generatort(): mode(ID_unknown) { }

  void set_mode(irep_idt _mode)
  {
    // only C and java modes supported
    assert((_mode==ID_java) || (_mode==ID_C));
    mode=_mode;
  }

  inline irep_idt &get_mode() { return mode; }

  unsignedbv_typet get_char_type() const;
  inline signedbv_typet get_index_type() const
  { return refined_string_typet::index_type(); }

  // Axioms are of three kinds: universally quantified string constraint,
  // not contains string constraints and simple formulas.
  std::vector<exprt> axioms;

  // Boolean symbols for the results of some string functions
  std::vector<symbol_exprt> boolean_symbols;

  // Symbols used in existential quantifications
  std::vector<symbol_exprt> index_symbols;

  // Used to store information about witnesses for not_contains constraints
  std::map<string_not_contains_constraintt, symbol_exprt> witness;

  inline exprt get_witness_of
  (const string_not_contains_constraintt & c, const exprt & univ_val) const
  { return index_exprt(witness.at(c), univ_val); }

  // Generates fresh indexes
  symbol_exprt fresh_exist_index(const irep_idt &prefix);
  symbol_exprt fresh_univ_index(const irep_idt &prefix);

  // Generates a fresh Boolean variable
  symbol_exprt fresh_boolean(const irep_idt &prefix);

  // We maintain a map from symbols to strings.
  std::map<irep_idt, string_exprt> symbol_to_string;

  // If a symbol is not yet present we will create a new one with
  // the correct type depending on whether the mode is java or c
  string_exprt find_or_add_string_of_symbol(const symbol_exprt & sym);

  inline void assign_to_symbol
  (const symbol_exprt & sym, const string_exprt & expr)
  { symbol_to_string[sym.get_identifier()]= expr; }


  // Add to the list of axioms, lemmas which should hold for the string to be
  // equal to the given expression.
  //  string_exprt create_string_equal_to_expr(const exprt & unrefined_string);

  string_exprt add_axioms_for_string_expr(const exprt & expr);
  void set_string_symbol_equal_to_expr
  (const symbol_exprt & sym, const exprt & str);

  // The following functions convert different string functions
  // and add the corresponding lemmas to a list of properties to be checked
  exprt add_axioms_for_function_application
  (const function_application_exprt &expr);


private:
  // The following functions add axioms for the returned value
  // to be equal to the result of the function given as argument.
  // They are not accessed directly from other classes: they call
  // `add_axioms_for_function_application` which determines which of
  // these methodes should be called.

  // Add axioms corresponding to the String.charAt java function
  exprt add_axioms_for_char_at(const function_application_exprt &f);

  // Add axioms corresponding to the String.codePointAt java function
  exprt add_axioms_for_code_point_at(const function_application_exprt &f);

  // Add axioms corresponding to the String.codePointBefore java function
  exprt add_axioms_for_code_point_before(const function_application_exprt &f);

  // Add axioms corresponding to the String.contains java function
  exprt add_axioms_for_contains(const function_application_exprt &f);

  // Add axioms corresponding to the String.equals java function
  exprt add_axioms_for_equals(const function_application_exprt &f);

  // Add axioms corresponding to the String.equalsIgnoreCase java function
  exprt add_axioms_for_equals_ignore_case(const function_application_exprt &f);

  // Add axioms for accessing the data field of java strings
  exprt add_axioms_for_data(const function_application_exprt &f);

  // Add axioms corresponding to the String.hashCode java function
  // The specification is partial: the actual value is not actualy computed
  // but we ensure that hash codes of equal strings are equal.
  exprt add_axioms_for_hash_code(const function_application_exprt &f);

  // Add axioms corresponding to the String.isEmpty java function
  exprt add_axioms_for_is_empty(const function_application_exprt &f);

  // Add axioms corresponding to the String.isPrefix java function
  exprt add_axioms_for_is_prefix
  (const string_exprt &prefix, const string_exprt &str, const exprt & offset);
  exprt add_axioms_for_is_prefix
  (const function_application_exprt &f, bool swap_arguments=false);

  // Add axioms corresponding to the String.isSuffix java function
  exprt add_axioms_for_is_suffix
  (const function_application_exprt &f, bool swap_arguments=false);

  // Add axioms corresponding to the String.length java function
  exprt add_axioms_for_length(const function_application_exprt &f);

  // Add axioms corresponding to the empty string ""
  string_exprt add_axioms_for_empty_string(const function_application_exprt &f);

  // Add axioms corresponding to the StringBuilder.setCharAt java function
  string_exprt add_axioms_for_char_set(const function_application_exprt &expr);

  // Add axioms for making a copy of a string
  string_exprt add_axioms_for_copy(const function_application_exprt &f);

  // Add axioms corresponding to the String.concat(String) java function
  string_exprt add_axioms_for_concat
  (const string_exprt & s1, const string_exprt & s2);
  string_exprt add_axioms_for_concat(const function_application_exprt &f);

  // Add axioms corresponding to the StringBuilder.append(I) java function
  string_exprt add_axioms_for_concat_int(const function_application_exprt &f);

  // Add axioms corresponding to the StringBuilder.append(J) java function
  string_exprt add_axioms_for_concat_long(const function_application_exprt &f);

  // Add axioms corresponding to the StringBuilder.append(Z) java function
  string_exprt add_axioms_for_concat_bool(const function_application_exprt &f);

  // Add axioms corresponding to the StringBuilder.append(C) java function
  string_exprt add_axioms_for_concat_char(const function_application_exprt &f);

  // Add axioms corresponding to the StringBuilder.append(D) java function
  string_exprt add_axioms_for_concat_double
  (const function_application_exprt &f);

  // Add axioms corresponding to the StringBuilder.append(F) java function
  string_exprt add_axioms_for_concat_float(const function_application_exprt &f);

  // Add axioms corresponding to the StringBuilder.appendCodePoint(F) function
  string_exprt add_axioms_for_concat_code_point
  (const function_application_exprt &f);

  // Add axioms from a string constant
  string_exprt add_axioms_for_constant
  (irep_idt sval, int char_width, unsignedbv_typet char_type);
  string_exprt add_axioms_for_constant(irep_idt sval);

  // Add axioms corresponding to the StringBuilder.delete java function
  string_exprt add_axioms_for_delete
  (const string_exprt &str, const exprt & start, const exprt & end);
  string_exprt add_axioms_for_delete(const function_application_exprt &expr);

  // Add axioms corresponding to the StringBuilder.deleteCharAt java function
  string_exprt add_axioms_for_delete_char_at
  (const function_application_exprt &expr);

  // Add axioms corresponding to the StringBuilder.insert java functions
  string_exprt add_axioms_for_insert
  (const string_exprt & s1, const string_exprt & s2, const exprt &offset);
  string_exprt add_axioms_for_insert(const function_application_exprt &f);
  string_exprt add_axioms_for_insert_int(const function_application_exprt &f);
  string_exprt add_axioms_for_insert_long(const function_application_exprt &f);
  string_exprt add_axioms_for_insert_bool(const function_application_exprt &f);
  string_exprt add_axioms_for_insert_char(const function_application_exprt &f);
  string_exprt add_axioms_for_insert_double
  (const function_application_exprt &f);
  string_exprt add_axioms_for_insert_float(const function_application_exprt &f);
  string_exprt add_axioms_for_insert_char_array
  (const function_application_exprt &f);

  // Add axioms for a string literal (calls `add_axioms_for_constant` with the
  // right parameters)
  string_exprt add_axioms_from_literal(const function_application_exprt &f);

  // Add axioms corresponding to the String.valueOf(I) java function
  string_exprt add_axioms_from_int(const function_application_exprt &f);
  string_exprt add_axioms_from_int(const exprt &i, size_t max_size);

  // Add axioms corresponding to the Integer.toHexString(I) java function
  string_exprt add_axioms_from_int_hex(const exprt &i);
  string_exprt add_axioms_from_int_hex(const function_application_exprt &f);

  // Add axioms corresponding to the String.valueOf(J) java function
  string_exprt add_axioms_from_long(const function_application_exprt &f);
  string_exprt add_axioms_from_long(const exprt &i, size_t max_size);

  // Add axioms corresponding to the String.valueOf(Z) java function
  string_exprt add_axioms_from_bool(const function_application_exprt &f);
  string_exprt add_axioms_from_bool(const exprt &i);

  // Add axioms corresponding to the String.valueOf(C) java function
  string_exprt add_axioms_from_char(const function_application_exprt &f);
  string_exprt add_axioms_from_char(const exprt &i);

  // Add axioms corresponding to the StringBuilder.insert:(I[CII) java function
  string_exprt add_axioms_from_char_array(const function_application_exprt &f);
  string_exprt add_axioms_from_char_array(
    const exprt & length,
    const exprt & data,
    const exprt & offset,
    const exprt & count);

  // Add axioms corresponding to the String.indexOf:(CI) java function
  exprt add_axioms_for_index_of(
    const string_exprt &str,
    const exprt & c,
    const exprt & from_index);

  // Add axioms corresponding to the String.indexOf:(String;I) java function
  // Warning: the specifications are only partial
  exprt add_axioms_for_index_of_string(
    const string_exprt &str,
    const string_exprt & substring,
    const exprt & from_index);

  // Add axioms corresponding to the String.indexOf java functions
  // Warning: the specifications are only partial for some of them
  exprt add_axioms_for_index_of(const function_application_exprt &f);

  // Add axioms corresponding to the String.lastIndexOf:(String;I) java function
  // Warning: the specifications are only partial
  exprt add_axioms_for_last_index_of_string(
    const string_exprt &str,
    const string_exprt & substring,
    const exprt & from_index);

  // Add axioms corresponding to the String.lastIndexOf:(CI) java function
  exprt add_axioms_for_last_index_of(
    const string_exprt &str,
    const exprt & c,
    const exprt & from_index);

  // Add axioms corresponding to the String.lastIndexOf java functions
  // Warning: the specifications are only partial for some of them
  exprt add_axioms_for_last_index_of(const function_application_exprt &f);

  // Add axioms corresponding to the String.valueOf(F) java function
  // Warning: the specifications of these functions is only partial
  string_exprt add_axioms_from_float(const function_application_exprt &f);
  string_exprt add_axioms_from_float(
    const exprt &f,
    bool double_precision=false);

  // Add axioms corresponding to the String.valueOf(D) java function
  // Warning: the specifications is only partial
  string_exprt add_axioms_from_double(const function_application_exprt &f);

  // Add axioms corresponding to the String.replace java function
  string_exprt add_axioms_for_replace(const function_application_exprt &f);

  // Add axioms corresponding to the StringBuilder.setLength java function
  string_exprt add_axioms_for_set_length(const function_application_exprt &f);

  // Add axioms corresponding to the String.substring java function
  // Warning: the specification may not be correct for the
  // case where the string is not long enough
  string_exprt add_axioms_for_substring
  (const string_exprt & str, const exprt & start, const exprt & end);
  string_exprt add_axioms_for_substring(const function_application_exprt &expr);

  // Add axioms corresponding to the String.toLowerCase java function
  string_exprt add_axioms_for_to_lower_case
  (const function_application_exprt &expr);

  // Add axioms corresponding to the String.toUpperCase java function
  string_exprt add_axioms_for_to_upper_case
  (const function_application_exprt &expr);

  // Add axioms corresponding to the String.trim java function
  string_exprt add_axioms_for_trim(const function_application_exprt &expr);

  // Add axioms corresponding to the String.valueOf([CII) function
  // Warning: not working correctly at the moment
  string_exprt add_axioms_for_value_of(const function_application_exprt &f);

  // Add axioms for converting a integer representing a code point to a utf-16
  // string
  string_exprt add_axioms_for_code_point(const exprt &code_point);

  // Add axioms corresponding to the String.valueOf([C) java function
  string_exprt add_axioms_for_java_char_array(const exprt & char_array);

  // Add axioms for an if expression that should return a string
  string_exprt add_axioms_for_if(const if_exprt &expr);

  // Add axioms for a character litteral (of the form 'c') to a string
  exprt add_axioms_for_char_literal(const function_application_exprt &f);

  // Add axioms corresponding the String.codePointCount java function
  // Warning: this function is underspecified, we do not compute the exact value
  // but over approximate it.
  exprt add_axioms_for_code_point_count(const function_application_exprt &f);

  // Add axioms corresponding the String.offsetByCodePointCount java function
  // Warning: this function is underspecified, it should return the index within
  // this String that is offset from the given first argument by second argument
  // code points and we approximate this by saying the result is
  // between index + offset and index + 2 * offset
  exprt add_axioms_for_offset_by_code_point
  (const function_application_exprt &f);

  // Add axioms corresponding to the Integer.parseInt java function
  exprt add_axioms_for_parse_int(const function_application_exprt &f);

  // Add axioms corresponding to the String.toCharArray java function
  exprt add_axioms_for_to_char_array(const function_application_exprt &f);

  // Add axioms corresponding to the String.compareTo java function
  exprt add_axioms_for_compare_to(const function_application_exprt &f);

  // Add axioms corresponding to the String.intern java function
  // Warning: this does not work at the moment because of the way we treat
  // string pointers
  symbol_exprt add_axioms_for_intern(const function_application_exprt &f);

  // Tells which language is used. C and Java are supported
  irep_idt mode;

  // assert that the number of argument is equal to nb and extract them
  inline static function_application_exprt::argumentst args
  (const function_application_exprt &expr, size_t nb)
  {
    function_application_exprt::argumentst args = expr.arguments();
    assert(args.size()==nb);
    return args;
  }

  constant_exprt constant_char(int i) const;
  size_t get_char_width() const;
  exprt int_of_hex_char(exprt chr, unsigned char_width, typet char_type) const;
  exprt is_high_surrogate(const exprt & chr) const;
  exprt is_low_surrogate(const exprt & chr) const;

  // Pool used for the intern method
  std::map<string_exprt, symbol_exprt> pool;

  // Used to determine whether hashcode should be equal
  std::map<string_exprt, symbol_exprt> hash;
};

#endif
