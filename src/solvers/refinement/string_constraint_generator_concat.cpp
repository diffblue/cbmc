/*******************************************************************\

Module: Generates string constraints for functions adding content
        add the end of strings

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for functions adding content add the end of
///   strings

#include <solvers/refinement/string_constraint_generator.h>

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
/// \param res: an array of characters expression
/// \param s1: an array of characters expression
/// \param s2: an array of characters expression
/// \param start_index: integer expression
/// \param end_index: integer expression
/// \return integer expression `0`
exprt string_constraint_generatort::add_axioms_for_concat_substr(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2,
  const exprt &start_index,
  const exprt &end_index)
{
  const typet &index_type = start_index.type();
  const exprt start1 = maximum(start_index, from_integer(0, index_type));
  const exprt end1 = maximum(minimum(end_index, s2.length()), start1);

  // Axiom 1.
  lemmas.push_back(
    length_constraint_for_concat_substr(res, s1, s2, start_index, end_index));

  // Axiom 2.
  constraints.push_back([&] { // NOLINT
    const symbol_exprt idx =
      fresh_univ_index("QA_index_concat", res.length().type());
    return string_constraintt(idx, s1.length(), equal_exprt(s1[idx], res[idx]));
  }());

  // Axiom 3.
  constraints.push_back([&] { // NOLINT
    const symbol_exprt idx2 =
      fresh_univ_index("QA_index_concat2", res.length().type());
    const equal_exprt res_eq(
      res[plus_exprt(idx2, s1.length())], s2[plus_exprt(start1, idx2)]);
    const minus_exprt upper_bound(res.length(), s1.length());
    return string_constraintt(idx2, upper_bound, res_eq);
  }());

  return from_integer(0, get_return_code_type());
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

/// Add axioms enforcing that `res` is the concatenation of `s1` with
/// character `c`.
/// These axioms are :
///   * \f$ |res|=|s1|+1 \f$
///   * \f$ \forall i<|s1|. res[i]=s1[i] \f$
///   * \f$ res[|s1|]=c \f$
///
/// \param res: string expression
/// \param s1: string expression
/// \param c: character expression
/// \return code 0 on success
exprt string_constraint_generatort::add_axioms_for_concat_char(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const exprt &c)
{
  const typet &index_type = res.length().type();
  lemmas.push_back(length_constraint_for_concat_char(res, s1));

  symbol_exprt idx = fresh_univ_index("QA_index_concat_char", index_type);
  string_constraintt a2(idx, s1.length(), equal_exprt(s1[idx], res[idx]));
  constraints.push_back(a2);

  equal_exprt a3(res[s1.length()], c);
  lemmas.push_back(a3);

  // We should have a enum type for the possible error codes
  return from_integer(0, get_return_code_type());
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
/// \param res: string_expression corresponding to the result
/// \param s1: the string expression to append to
/// \param s2: the string expression to append to the first one
/// \return an integer expression
exprt string_constraint_generatort::add_axioms_for_concat(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2)
{
  exprt index_zero=from_integer(0, s2.length().type());
  return add_axioms_for_concat_substr(res, s1, s2, index_zero, s2.length());
}

/// String concatenation
///
/// This primitive accepts 4 or 6 arguments.
/// \copybrief string_constraint_generatort::add_axioms_for_concat_substr
/// \link string_constraint_generatort::add_axioms_for_concat_substr
///   (More...) \endlink
///
/// \param f: function application with arguments integer `|res|`, character
///           pointer `&res[0]`, refined_string `s1`, refined_string `s2`,
///           optional integer `start_index`, optional integer `end_index`
/// \return an integer expression
exprt string_constraint_generatort::add_axioms_for_concat(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  PRECONDITION(args.size() == 4 || args.size() == 6);
  const array_string_exprt s1 = get_string_expr(args[2]);
  const array_string_exprt s2 = get_string_expr(args[3]);
  const array_string_exprt res = char_array_of_pointer(args[1], args[0]);
  if(args.size() == 6)
    return add_axioms_for_concat_substr(res, s1, s2, args[4], args[5]);
  else // args.size()==4
    return add_axioms_for_concat(res, s1, s2);
}

/// Add axioms enforcing that the string represented by the two first
/// expressions is equal to the concatenation of the string argument and
/// the character argument of the function application.
/// \todo This should be merged with add_axioms_for_concat.
/// \param f: function application with a length, pointer, string and character
///           argument.
/// \return code 0 on success
exprt string_constraint_generatort::add_axioms_for_concat_char(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  PRECONDITION(args.size() == 4);
  const array_string_exprt s1 = get_string_expr(args[2]);
  const exprt &c = args[3];
  const array_string_exprt res = char_array_of_pointer(args[1], args[0]);
  return add_axioms_for_concat_char(res, s1, c);
}

/// Add axioms corresponding to the StringBuilder.appendCodePoint(I) function
/// \deprecated java specific
/// \param f: function application with two arguments: a string and a code point
/// \return an expression
exprt string_constraint_generatort::add_axioms_for_concat_code_point(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 4);
  const array_string_exprt res =
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const array_string_exprt s1 = get_string_expr(f.arguments()[2]);
  const typet &char_type = s1.content().type().subtype();
  const typet &index_type = s1.length().type();
  const array_string_exprt code_point = fresh_string(index_type, char_type);
  const exprt return_code1 =
    add_axioms_for_code_point(code_point, f.arguments()[3]);
  return add_axioms_for_concat(res, s1, code_point);
}
