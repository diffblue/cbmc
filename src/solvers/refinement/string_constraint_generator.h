/*******************************************************************\

Module: Generates string constraints to link results from string functions
        with their arguments. This is inspired by the PASS paper at HVC'13:
        "PASS: String Solving with Parameterized Array and Interval Automaton"
        by Guodong Li and Indradeep Ghosh, which gives examples of constraints
        for several functions.

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints to link results from string functions with
///   their arguments. This is inspired by the PASS paper at HVC'13: "PASS:
///   String Solving with Parameterized Array and Interval Automaton" by Guodong
///   Li and Indradeep Ghosh, which gives examples of constraints for several
///   functions.

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_GENERATOR_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_CONSTRAINT_GENERATOR_H

#include <limits>
#include <util/string_expr.h>
#include <util/replace_expr.h>
#include <util/refined_string_type.h>
#include <util/constexpr.def>
#include <solvers/refinement/string_constraint.h>

class string_constraint_generatort final
{
public:
  // This module keeps a list of axioms. It has methods which generate
  // string constraints for different string functions and add them
  // to the axiom list.

  // Used by format function
  class format_specifiert;

  /// Arguments pack for the string_constraint_generator constructor
  struct infot
  {
    /// Max length of non-deterministic strings
    size_t string_max_length=std::numeric_limits<size_t>::max();
  };

  string_constraint_generatort(const infot& info, const namespacet& ns);

  /// Axioms are of three kinds: universally quantified string constraint,
  /// not contains string constraints and simple formulas.
  const std::vector<exprt> &get_lemmas() const;
  const std::vector<string_constraintt> &get_constraints() const;
  const std::vector<string_not_contains_constraintt> &
  get_not_contains_constraints() const;

  /// Boolean symbols for the results of some string functions
  const std::vector<symbol_exprt> &get_boolean_symbols() const;

  /// Symbols used in existential quantifications
  const std::vector<symbol_exprt> &get_index_symbols() const;

  /// Set of strings that have been created by the generator
  const std::set<array_string_exprt> &get_created_strings() const;

  exprt get_witness_of(
    const string_not_contains_constraintt &c,
    const exprt &univ_val) const
  {
    return index_exprt(witness.at(c), univ_val);
  }

  symbol_exprt fresh_symbol(
    const irep_idt &prefix, const typet &type=bool_typet());
  symbol_exprt fresh_univ_index(const irep_idt &prefix, const typet &type);


  exprt add_axioms_for_function_application(
    const function_application_exprt &expr);

  symbol_exprt fresh_exist_index(const irep_idt &prefix, const typet &type);

  const std::map<exprt, array_string_exprt> &get_arrays_of_pointers() const
  {
    return arrays_of_pointers_;
  }

  exprt get_length_of_string_array(const array_string_exprt &s) const;

  // Type used by primitives to signal errors
  const signedbv_typet get_return_code_type()
  {
    return signedbv_typet(32);
  }

private:
  symbol_exprt fresh_boolean(const irep_idt &prefix);
  array_string_exprt
  fresh_string(const typet &index_type, const typet &char_type);
  array_string_exprt get_string_expr(const exprt &expr);
  plus_exprt plus_exprt_with_overflow_check(const exprt &op1, const exprt &op2);

  array_string_exprt associate_char_array_to_char_pointer(
    const exprt &char_pointer,
    const typet &char_array_type);

  static constant_exprt constant_char(int i, const typet &char_type);

  array_string_exprt
  char_array_of_pointer(const exprt &pointer, const exprt &length);

  void add_default_axioms(const array_string_exprt &s);
  exprt axiom_for_is_positive_index(const exprt &x);

  void add_constraint_on_characters(
    const array_string_exprt &s,
    const exprt &start,
    const exprt &end,
    const std::string &char_set);
  exprt
  add_axioms_for_constrain_characters(const function_application_exprt &f);

  // The following functions add axioms for the returned value
  // to be equal to the result of the function given as argument.
  // They are not accessed directly from other classes: they call
  // `add_axioms_for_function_application` which determines which of
  // these methods should be called.

  exprt add_axioms_for_char_at(const function_application_exprt &f);
  exprt add_axioms_for_code_point_at(const function_application_exprt &f);
  exprt add_axioms_for_code_point_before(const function_application_exprt &f);
  exprt add_axioms_for_contains(const function_application_exprt &f);
  exprt add_axioms_for_equals(const function_application_exprt &f);
  exprt add_axioms_for_equals_ignore_case(const function_application_exprt &f);

  // Add axioms corresponding to the String.hashCode java function
  // The specification is partial: the actual value is not actually computed
  // but we ensure that hash codes of equal strings are equal.
  exprt add_axioms_for_hash_code(const function_application_exprt &f);

  exprt add_axioms_for_is_empty(const function_application_exprt &f);
  exprt add_axioms_for_is_prefix(
    const array_string_exprt &prefix,
    const array_string_exprt &str,
    const exprt &offset);
  exprt add_axioms_for_is_prefix(
    const function_application_exprt &f, bool swap_arguments=false);
  exprt add_axioms_for_is_suffix(
    const function_application_exprt &f, bool swap_arguments=false);
  exprt add_axioms_for_length(const function_application_exprt &f);
  exprt add_axioms_for_empty_string(const function_application_exprt &f);
  exprt add_axioms_for_char_set(const function_application_exprt &f);
  exprt add_axioms_for_copy(const function_application_exprt &f);
  exprt add_axioms_for_concat(
    const array_string_exprt &res,
    const array_string_exprt &s1,
    const array_string_exprt &s2);
  exprt add_axioms_for_concat_char(
    const array_string_exprt &res,
    const array_string_exprt &s1,
    const exprt &c);
  exprt add_axioms_for_concat_char(const function_application_exprt &f);
  exprt add_axioms_for_concat_substr(
    const array_string_exprt &res,
    const array_string_exprt &s1,
    const array_string_exprt &s2,
    const exprt &start_index,
    const exprt &end_index);
  exprt add_axioms_for_concat(const function_application_exprt &f);
  exprt add_axioms_for_concat_code_point(const function_application_exprt &f);
  exprt add_axioms_for_constant(
    const array_string_exprt &res,
    irep_idt sval,
    const exprt &guard = true_exprt());

  exprt add_axioms_for_delete(
    const array_string_exprt &res,
    const array_string_exprt &str,
    const exprt &start,
    const exprt &end);
  exprt add_axioms_for_delete(const function_application_exprt &f);
  exprt add_axioms_for_delete_char_at(const function_application_exprt &expr);
  exprt add_axioms_for_format(const function_application_exprt &f);
  exprt add_axioms_for_format(
    const array_string_exprt &res,
    const std::string &s,
    const exprt::operandst &args);

  array_string_exprt add_axioms_for_format_specifier(
    const format_specifiert &fs,
    const struct_exprt &arg,
    const typet &index_type,
    const typet &char_type);

  exprt add_axioms_for_insert(
    const array_string_exprt &res,
    const array_string_exprt &s1,
    const array_string_exprt &s2,
    const exprt &offset);
  exprt add_axioms_for_insert(const function_application_exprt &f);
  exprt add_axioms_for_insert_int(const function_application_exprt &f);
  exprt add_axioms_for_insert_bool(const function_application_exprt &f);
  exprt add_axioms_for_insert_char(const function_application_exprt &f);
  exprt add_axioms_for_insert_float(const function_application_exprt &f);
  exprt add_axioms_for_insert_double(const function_application_exprt &f);

  exprt add_axioms_for_cprover_string(
    const array_string_exprt &res,
    const exprt &arg,
    const exprt &guard);
  exprt add_axioms_from_literal(const function_application_exprt &f);
  exprt add_axioms_from_int(const function_application_exprt &f);
  exprt add_axioms_from_int(
    const array_string_exprt &res,
    const exprt &input_int,
    size_t max_size = 0);
  exprt add_axioms_from_int_with_radix(
    const array_string_exprt &res,
    const exprt &input_int,
    const exprt &radix,
    size_t max_size = 0);
  exprt add_axioms_from_int_hex(const array_string_exprt &res, const exprt &i);
  exprt add_axioms_from_int_hex(const function_application_exprt &f);
  exprt add_axioms_from_long(const function_application_exprt &f);
  exprt add_axioms_from_bool(const function_application_exprt &f);
  exprt add_axioms_from_bool(const array_string_exprt &res, const exprt &i);
  exprt add_axioms_from_char(const function_application_exprt &f);
  exprt add_axioms_from_char(const array_string_exprt &res, const exprt &i);
  exprt add_axioms_for_index_of(
    const array_string_exprt &str,
    const exprt &c,
    const exprt &from_index);
  exprt add_axioms_for_index_of_string(
    const array_string_exprt &haystack,
    const array_string_exprt &needle,
    const exprt &from_index);
  exprt add_axioms_for_index_of(const function_application_exprt &f);
  exprt add_axioms_for_last_index_of_string(
    const array_string_exprt &haystack,
    const array_string_exprt &needle,
    const exprt &from_index);
  exprt add_axioms_for_last_index_of(
    const array_string_exprt &str,
    const exprt &c,
    const exprt &from_index);

  exprt add_axioms_for_last_index_of(const function_application_exprt &f);

  /// \todo The specifications of these functions is only partial.
  /// We currently only specify that the string for NaN is "NaN", for infinity
  /// and minus infinity the string are "Infinity" and "-Infinity respectively
  /// otherwise the string contains only characters in [0123456789.] and '-' at
  /// the start for negative number
  exprt add_axioms_for_string_of_float(const function_application_exprt &f);
  exprt
  add_axioms_for_string_of_float(const array_string_exprt &res, const exprt &f);
  exprt add_axioms_for_fractional_part(
    const array_string_exprt &res,
    const exprt &i,
    size_t max_size);
  exprt add_axioms_from_float_scientific_notation(
    const array_string_exprt &res,
    const exprt &f);
  exprt add_axioms_from_float_scientific_notation(
    const function_application_exprt &f);

  /// Add axioms corresponding to the String.valueOf(D) java function
  /// \todo The specifications is only partial.
  exprt add_axioms_from_double(const function_application_exprt &f);

  exprt add_axioms_for_replace(const function_application_exprt &f);
  exprt add_axioms_for_set_length(const function_application_exprt &f);

  /// \todo The specification may not be correct for the case where the
  /// string is shorter than end. An actual java program should throw an
  /// exception in that case.
  exprt add_axioms_for_substring(
    const array_string_exprt &res,
    const array_string_exprt &str,
    const exprt &start,
    const exprt &end);
  exprt add_axioms_for_substring(const function_application_exprt &f);
  exprt add_axioms_for_to_lower_case(const function_application_exprt &f);
  exprt add_axioms_for_to_upper_case(const function_application_exprt &f);
  exprt add_axioms_for_to_upper_case(
    const array_string_exprt &res,
    const array_string_exprt &expr);
  exprt add_axioms_for_trim(const function_application_exprt &f);

  exprt add_axioms_for_code_point(
    const array_string_exprt &res,
    const exprt &code_point);
  exprt add_axioms_for_char_literal(const function_application_exprt &f);

  /// Add axioms corresponding the String.codePointCount java function
  /// \todo This function is underspecified, we do not compute the exact value
  /// but over approximate it.
  /// \deprecated This is Java specific and should be implemented in Java.
  exprt add_axioms_for_code_point_count(const function_application_exprt &f);

  /// Add axioms corresponding the String.offsetByCodePointCount java function
  /// \todo This function is underspecified, it should return the index within
  /// this String that is offset from the given first argument by second
  /// argument code points and we approximate this by saying the result is
  /// between index + offset and index + 2 * offset.
  /// \deprecated This is Java specific and should be implemented in Java.
  exprt add_axioms_for_offset_by_code_point(
    const function_application_exprt &f);

  void add_axioms_for_characters_in_integer_string(
    const exprt &input_int,
    const typet &type,
    const bool strict_formatting,
    const array_string_exprt &str,
    const std::size_t max_string_length,
    const exprt &radix,
    const unsigned long radix_ul);
  void add_axioms_for_correct_number_format(
    const exprt &input_int,
    const array_string_exprt &str,
    const exprt &radix_as_char,
    const unsigned long radix_ul,
    const std::size_t max_size,
    const bool strict_formatting);
  exprt add_axioms_for_parse_int(const function_application_exprt &f);
  exprt add_axioms_for_compare_to(const function_application_exprt &f);

  /// Add axioms corresponding to the String.intern java function
  /// \todo This does not work at the moment because of the way we treat
  /// string pointers.
  /// \deprecated Not tested.
  symbol_exprt add_axioms_for_intern(const function_application_exprt &f);

  exprt associate_array_to_pointer(const function_application_exprt &f);

  exprt associate_length_to_array(const function_application_exprt &f);

  // Helper functions
  static exprt int_of_hex_char(const exprt &chr);
  static exprt is_high_surrogate(const exprt &chr);
  static exprt is_low_surrogate(const exprt &chr);
  static exprt character_equals_ignore_case(
    exprt char1, exprt char2, exprt char_a, exprt char_A, exprt char_Z);
  unsigned long to_integer_or_default(const exprt &expr, unsigned long def);

  // MEMBERS
public:
  const size_t max_string_length;
  // Used to store information about witnesses for not_contains constraints
  std::map<string_not_contains_constraintt, symbol_exprt> witness;
private:
  std::set<array_string_exprt> created_strings;
  unsigned symbol_count=0;
  const messaget message;

  std::vector<exprt> lemmas;
  std::vector<string_constraintt> constraints;
  std::vector<string_not_contains_constraintt> not_contains_constraints;
  std::vector<symbol_exprt> boolean_symbols;
  std::vector<symbol_exprt> index_symbols;
  const namespacet ns;
  // To each string on which hash_code was called we associate a symbol
  // representing the return value of the hash_code function.
  std::map<array_string_exprt, exprt> hash_code_of_string;

  // Pool used for the intern method
  std::map<array_string_exprt, symbol_exprt> intern_of_string;

  // associate arrays to char pointers
  std::map<exprt, array_string_exprt> arrays_of_pointers_;

  // associate length to arrays of infinite size
  std::map<array_string_exprt, symbol_exprt> length_of_array_;
};

exprt is_digit_with_radix(
  const exprt &chr,
  const bool strict_formatting,
  const exprt &radix_as_char,
  const unsigned long radix_ul);

exprt get_numeric_value_from_character(
  const exprt &chr,
  const typet &char_type,
  const typet &type,
  const bool strict_formatting,
  unsigned long radix_ul);

size_t max_printed_string_length(const typet &type, unsigned long ul_radix);

std::string
utf16_constant_array_to_java(const array_exprt &arr, std::size_t length);

#endif
