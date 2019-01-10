/*******************************************************************\

Module: Generates string constraints for functions adding content
        add the end of strings

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for functions adding content add the end of
///   strings

#include "string_constraint_generator.h"

/// Add axioms enforcing that `res` is the concatenation of `s1` with
/// the substring of `s2` starting at index `start_index'` and ending
/// at index `end_index'`.
/// Where start_index' is max(0, start_index) and end_index' is
/// max(min(end_index, s2.length), start_index')
/// If s1.length + end_index' - start_index' is greater than the maximal integer
/// of the type of res.length, then the result gets truncated to the size
/// of this maximal integer.
///
/// These axioms are:
///   1. \f$|res| = overflow ? |s_1| + end\_index' - start\_index'
///                          : max_int \f$
///   2. \f$\forall i<|s_1|. res[i]=s_1[i] \f$
///   3. \f$\forall i< |res| - |s_1|.\ res[i+|s_1|] = s_2[start\_index'+i]\f$
///
/// \param fresh_symbol: generator of fresh symbols
/// \param res: an array of characters expression
/// \param s1: an array of characters expression
/// \param s2: an array of characters expression
/// \param start_index: integer expression
/// \param end_index: integer expression
/// \return integer expression `0`
std::pair<exprt, string_constraintst> add_axioms_for_concat_substr(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2,
  const exprt &start_index,
  const exprt &end_index)
{
  string_constraintst constraints;
  const typet &index_type = start_index.type();
  const exprt start1 = maximum(start_index, from_integer(0, index_type));
  const exprt end1 = maximum(minimum(end_index, s2.length()), start1);

  // Axiom 1.
  constraints.existential.push_back(
    length_constraint_for_concat_substr(res, s1, s2, start_index, end_index));

  // Axiom 2.
  constraints.universal.push_back([&] {
    const symbol_exprt idx =
      fresh_symbol("QA_index_concat", res.length().type());
    return string_constraintt(
      idx, zero_if_negative(s1.length()), equal_exprt(s1[idx], res[idx]));
  }());

  // Axiom 3.
  constraints.universal.push_back([&] {
    const symbol_exprt idx2 =
      fresh_symbol("QA_index_concat2", res.length().type());
    const equal_exprt res_eq(
      res[plus_exprt(idx2, s1.length())], s2[plus_exprt(start1, idx2)]);
    const minus_exprt upper_bound(res.length(), s1.length());
    return string_constraintt(idx2, zero_if_negative(upper_bound), res_eq);
  }());

  return {from_integer(0, get_return_code_type()), std::move(constraints)};
}

/// Add axioms enforcing that the length of `res` is that of the concatenation
/// of `s1` with the substring of `s2` starting at index `start'`
/// and ending at index `end'`.
/// Where start_index' is max(0, start) and end' is
/// max(min(end, s2.length), start')
exprt length_constraint_for_concat_substr(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2,
  const exprt &start,
  const exprt &end)
{
  PRECONDITION(res.length().type().id() == ID_signedbv);
  const exprt start1 = maximum(start, from_integer(0, start.type()));
  const exprt end1 = maximum(minimum(end, s2.length()), start1);
  const plus_exprt res_length(s1.length(), minus_exprt(end1, start1));
  const exprt overflow = sum_overflows(res_length);
  const exprt max_int = to_signedbv_type(res.length().type()).largest_expr();
  return equal_exprt(res.length(), if_exprt(overflow, max_int, res_length));
}

/// Add axioms enforcing that the length of `res` is that of the concatenation
/// of `s1` with `s2`
exprt length_constraint_for_concat(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2)
{
  return equal_exprt(res.length(), plus_exprt(s1.length(), s2.length()));
}

/// Add axioms enforcing that the length of `res` is that of the concatenation
/// of `s1` with
exprt length_constraint_for_concat_char(
  const array_string_exprt &res,
  const array_string_exprt &s1)
{
  return equal_exprt(
    res.length(), plus_exprt(s1.length(), from_integer(1, s1.length().type())));
}

/// Add axioms enforcing that `res` is equal to the concatenation of `s1` and
/// `s2`.
///
/// \deprecated should use concat_substr instead
/// \param fresh_symbol: generator of fresh symbols
/// \param res: string_expression corresponding to the result
/// \param s1: the string expression to append to
/// \param s2: the string expression to append to the first one
/// \return an integer expression
std::pair<exprt, string_constraintst> add_axioms_for_concat(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2)
{
  exprt index_zero=from_integer(0, s2.length().type());
  return add_axioms_for_concat_substr(
    fresh_symbol, res, s1, s2, index_zero, s2.length());
}

/// Add axioms corresponding to the StringBuilder.appendCodePoint(I) function
/// \deprecated java specific
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with two arguments: a string and a code point
/// \param array_pool: pool of arrays representing strings
/// \return an expression
std::pair<exprt, string_constraintst> add_axioms_for_concat_code_point(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  PRECONDITION(f.arguments().size() == 4);
  const array_string_exprt res =
    char_array_of_pointer(array_pool, f.arguments()[1], f.arguments()[0]);
  const array_string_exprt s1 = get_string_expr(array_pool, f.arguments()[2]);
  const typet &char_type = s1.content().type().subtype();
  const typet &index_type = s1.length().type();
  const array_string_exprt code_point =
    array_pool.fresh_string(index_type, char_type);
  return combine_results(
    add_axioms_for_code_point(code_point, f.arguments()[3]),
    add_axioms_for_concat(fresh_symbol, res, s1, code_point));
}
