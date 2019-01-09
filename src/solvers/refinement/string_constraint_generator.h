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
#include <util/deprecate.h>
#include <solvers/refinement/string_constraint.h>

/// Generation of fresh symbols of a given type
class symbol_generatort final
{
public:
  symbol_exprt
  operator()(const irep_idt &prefix, const typet &type = bool_typet());

private:
  unsigned symbol_count = 0;

#ifdef DEBUG
public:
  /// Keep track of created symbols, for debugging purposes.
  std::vector<symbol_exprt> created_symbols;
#endif
};

/// Correspondance between arrays and pointers string representations
class array_poolt final
{
public:
  explicit array_poolt(symbol_generatort &symbol_generator)
    : fresh_symbol(symbol_generator)
  {
  }

  const std::unordered_map<exprt, array_string_exprt, irep_hash> &
  get_arrays_of_pointers() const
  {
    return arrays_of_pointers;
  }

  exprt get_length(const array_string_exprt &s) const;

  void insert(const exprt &pointer_expr, array_string_exprt &array);

  const array_string_exprt &find(const exprt &pointer, const exprt &length);

  const std::set<array_string_exprt> &created_strings() const;

  array_string_exprt
  fresh_string(const typet &index_type, const typet &char_type);

private:
  // associate arrays to char pointers
  std::unordered_map<exprt, array_string_exprt, irep_hash> arrays_of_pointers;

  // associate length to arrays of infinite size
  std::unordered_map<array_string_exprt, symbol_exprt, irep_hash>
    length_of_array;

  // generates fresh symbols
  symbol_generatort &fresh_symbol;

  // Strings created in the pool
  std::set<array_string_exprt> created_strings_value;

  array_string_exprt make_char_array_for_char_pointer(
    const exprt &char_pointer,
    const typet &char_array_type);
};

/// Converts a struct containing a length and pointer to an array.
/// This allows to get a string expression from arguments of a string
/// builtion function, because string arguments in these function calls
/// are given as a struct containing a length and pointer to an array.
array_string_exprt of_argument(array_poolt &array_pool, const exprt &arg);

const array_string_exprt &char_array_of_pointer(
  array_poolt &pool,
  const exprt &pointer,
  const exprt &length);

array_string_exprt get_string_expr(array_poolt &pool, const exprt &expr);

/// Collection of constraints of different types: existential formulas,
/// universal formulas, and "not contains" (universal with one alternation).
struct string_constraintst final
{
  std::vector<exprt> existential;
  std::vector<string_constraintt> universal;
  std::vector<string_not_contains_constraintt> not_contains;

  /// Clear all constraints
  void clear();
};

void merge(string_constraintst &result, string_constraintst other);

class string_constraint_generatort final
{
public:
  // This module keeps a list of axioms. It has methods which generate
  // string constraints for different string functions and add them
  // to the axiom list.

  explicit string_constraint_generatort(const namespacet &ns);

  std::pair<exprt, string_constraintst> add_axioms_for_function_application(
    const function_application_exprt &expr);

  symbol_generatort fresh_symbol;

  array_poolt array_pool;

  string_constraintst constraints;

  const namespacet ns;

  /// Associate array to pointer, and array to length
  /// \return an expression if the given function application is one of
  ///   associate pointer and associate length
  optionalt<exprt>
  make_array_pointer_association(const function_application_exprt &expr);

private:
  /// Add axioms corresponding to the String.intern java function
  /// \todo This does not work at the moment because of the way we treat
  /// string pointers.
  /// \deprecated Not tested.
  std::pair<symbol_exprt, string_constraintst> add_axioms_for_intern(
    const function_application_exprt &f);

  exprt associate_array_to_pointer(const function_application_exprt &f);

  exprt associate_length_to_array(const function_application_exprt &f);

  // Add axioms corresponding to the String.hashCode java function
  // The specification is partial: the actual value is not actually computed
  // but we ensure that hash codes of equal strings are equal.
  std::pair<exprt, string_constraintst> add_axioms_for_hash_code(
    const function_application_exprt &f,
    array_poolt &pool);

  // MEMBERS
  const messaget message;

  // To each string on which hash_code was called we associate a symbol
  // representing the return value of the hash_code function.
  std::map<array_string_exprt, exprt> hash_code_of_string;

  // Pool used for the intern method
  std::map<array_string_exprt, symbol_exprt> intern_of_string;
};

// Type used by primitives to signal errors
signedbv_typet get_return_code_type();

std::pair<exprt, string_constraintst> add_axioms_for_concat(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2);
std::pair<exprt, string_constraintst> add_axioms_for_concat_substr(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2,
  const exprt &start_index,
  const exprt &end_index);
std::pair<exprt, string_constraintst> add_axioms_for_insert(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2,
  const exprt &offset);
std::pair<exprt, string_constraintst> add_axioms_for_string_of_int_with_radix(
  const array_string_exprt &res,
  const exprt &input_int,
  const exprt &radix,
  size_t max_size,
  const namespacet &ns);

string_constraintst add_constraint_on_characters(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &s,
  const exprt &start,
  const exprt &end,
  const std::string &char_set);
std::pair<exprt, string_constraintst> add_axioms_for_constrain_characters(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);

// The following functions add axioms for the returned value
// to be equal to the result of the function given as argument.
// They are not accessed directly from other classes: they call
// `add_axioms_for_function_application` which determines which of
// these methods should be called.

std::pair<exprt, string_constraintst> add_axioms_for_char_at(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_for_code_point_at(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &pool);
std::pair<exprt, string_constraintst> add_axioms_for_code_point_before(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &pool);
std::pair<exprt, string_constraintst> add_axioms_for_contains(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_for_equals(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &pool);
std::pair<exprt, string_constraintst> add_axioms_for_equals_ignore_case(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &pool);

std::pair<exprt, string_constraintst> add_axioms_for_is_empty(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_for_is_prefix(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &prefix,
  const array_string_exprt &str,
  const exprt &offset);
std::pair<exprt, string_constraintst> add_axioms_for_is_prefix(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  bool swap_arguments,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_for_is_suffix(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  bool swap_arguments,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_for_length(
  const function_application_exprt &f,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_for_empty_string(
  const function_application_exprt &f);

std::pair<exprt, string_constraintst> add_axioms_for_copy(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);

std::pair<exprt, string_constraintst> add_axioms_for_concat_code_point(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_for_constant(
  const array_string_exprt &res,
  irep_idt sval,
  const exprt &guard = true_exprt());

std::pair<exprt, string_constraintst> add_axioms_for_delete(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const array_string_exprt &str,
  const exprt &start,
  const exprt &end,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_for_delete(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_for_delete_char_at(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &expr,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_for_format(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool,
  const messaget &message,
  const namespacet &ns);
std::pair<exprt, string_constraintst> add_axioms_for_format(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const std::string &s,
  const exprt::operandst &args,
  array_poolt &array_pool,
  const messaget &message,
  const namespacet &ns);

std::pair<exprt, string_constraintst> add_axioms_for_insert(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &pool);
std::pair<exprt, string_constraintst> add_axioms_for_insert_int(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool,
  const namespacet &ns);
std::pair<exprt, string_constraintst> add_axioms_for_insert_bool(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_for_insert_char(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_for_insert_float(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool,
  const namespacet &ns);
std::pair<exprt, string_constraintst> add_axioms_for_insert_double(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool,
  const namespacet &ns);

std::pair<exprt, string_constraintst> add_axioms_for_cprover_string(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const exprt &arg,
  const exprt &guard);
std::pair<exprt, string_constraintst> add_axioms_from_literal(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);

std::pair<exprt, string_constraintst> add_axioms_for_string_of_int(
  const array_string_exprt &res,
  const exprt &input_int,
  size_t max_size,
  const namespacet &ns);
std::pair<exprt, string_constraintst> add_axioms_from_int_hex(
  const array_string_exprt &res,
  const exprt &i);
std::pair<exprt, string_constraintst> add_axioms_from_int_hex(
  const function_application_exprt &f,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_from_long(
  const function_application_exprt &f,
  array_poolt &array_pool,
  const namespacet &ns);
std::pair<exprt, string_constraintst> add_axioms_from_bool(
  const function_application_exprt &f,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_from_bool(
  const array_string_exprt &res,
  const exprt &i);
std::pair<exprt, string_constraintst> add_axioms_from_char(
  const function_application_exprt &f,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_from_char(
  const array_string_exprt &res,
  const exprt &i);
std::pair<exprt, string_constraintst> add_axioms_for_index_of(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &str,
  const exprt &c,
  const exprt &from_index);
std::pair<exprt, string_constraintst> add_axioms_for_index_of_string(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &haystack,
  const array_string_exprt &needle,
  const exprt &from_index);
std::pair<exprt, string_constraintst> add_axioms_for_index_of(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_for_last_index_of_string(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &haystack,
  const array_string_exprt &needle,
  const exprt &from_index);
std::pair<exprt, string_constraintst> add_axioms_for_last_index_of(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &str,
  const exprt &c,
  const exprt &from_index);

std::pair<exprt, string_constraintst> add_axioms_for_last_index_of(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);

/// \todo The specifications of these functions is only partial.
/// We currently only specify that the string for NaN is "NaN", for infinity
/// and minus infinity the string are "Infinity" and "-Infinity respectively
/// otherwise the string contains only characters in [0123456789.] and '-' at
/// the start for negative number
std::pair<exprt, string_constraintst> add_axioms_for_string_of_float(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool,
  const namespacet &ns);
std::pair<exprt, string_constraintst> add_axioms_for_string_of_float(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const exprt &f,
  array_poolt &array_pool,
  const namespacet &ns);
std::pair<exprt, string_constraintst> add_axioms_for_fractional_part(
  const array_string_exprt &res,
  const exprt &i,
  size_t max_size);
std::pair<exprt, string_constraintst> add_axioms_from_float_scientific_notation(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const exprt &f,
  array_poolt &array_pool,
  const namespacet &ns);
std::pair<exprt, string_constraintst> add_axioms_from_float_scientific_notation(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool,
  const namespacet &ns);

/// Add axioms corresponding to the String.valueOf(D) java function
/// \todo The specifications is only partial.
std::pair<exprt, string_constraintst> add_axioms_from_double(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool,
  const namespacet &ns);

std::pair<exprt, string_constraintst> add_axioms_for_replace(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);
std::pair<exprt, string_constraintst> add_axioms_for_set_length(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);

/// \todo The specification may not be correct for the case where the
/// string is shorter than end. An actual java program should throw an
/// exception in that case.
std::pair<exprt, string_constraintst> add_axioms_for_substring(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const array_string_exprt &str,
  const exprt &start,
  const exprt &end);
std::pair<exprt, string_constraintst> add_axioms_for_substring(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);

std::pair<exprt, string_constraintst> add_axioms_for_trim(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);

std::pair<exprt, string_constraintst> add_axioms_for_code_point(
  const array_string_exprt &res,
  const exprt &code_point);
std::pair<exprt, string_constraintst> add_axioms_for_char_literal(
  const function_application_exprt &f);

/// Add axioms corresponding the String.codePointCount java function
/// \todo This function is underspecified, we do not compute the exact value
/// but over approximate it.
/// \deprecated This is Java specific and should be implemented in Java.
DEPRECATED("This is Java specific and should be implemented in Java")
std::pair<exprt, string_constraintst> add_axioms_for_code_point_count(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &pool);

/// Add axioms corresponding the String.offsetByCodePointCount java function
/// \todo This function is underspecified, it should return the index within
/// this String that is offset from the given first argument by second
/// argument code points and we approximate this by saying the result is
/// between index + offset and index + 2 * offset.
/// \deprecated This is Java specific and should be implemented in Java.
std::pair<exprt, string_constraintst> add_axioms_for_offset_by_code_point(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f);

string_constraintst add_axioms_for_characters_in_integer_string(
  const exprt &input_int,
  const typet &type,
  const bool strict_formatting,
  const array_string_exprt &str,
  const std::size_t max_string_length,
  const exprt &radix,
  const unsigned long radix_ul);
string_constraintst add_axioms_for_correct_number_format(
  const array_string_exprt &str,
  const exprt &radix_as_char,
  const unsigned long radix_ul,
  const std::size_t max_size,
  const bool strict_formatting);
std::pair<exprt, string_constraintst> add_axioms_for_parse_int(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool,
  const namespacet &ns);
std::pair<exprt, string_constraintst> add_axioms_for_compare_to(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);

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

exprt is_positive(const exprt &x);

/// \return expression representing the minimum of two expressions
exprt minimum(const exprt &a, const exprt &b);

/// \return expression representing the maximum of two expressions
exprt maximum(const exprt &a, const exprt &b);

/// \return Boolean true when the sum of the two expressions overflows
exprt sum_overflows(const plus_exprt &sum);

exprt length_constraint_for_concat_char(
  const array_string_exprt &res,
  const array_string_exprt &s1);
exprt length_constraint_for_concat(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2);
exprt length_constraint_for_concat_substr(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2,
  const exprt &start_index,
  const exprt &end_index);
exprt length_constraint_for_insert(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2);

exprt zero_if_negative(const exprt &expr);

std::pair<exprt, string_constraintst> combine_results(
  std::pair<exprt, string_constraintst> result1,
  std::pair<exprt, string_constraintst> result2);
#endif
