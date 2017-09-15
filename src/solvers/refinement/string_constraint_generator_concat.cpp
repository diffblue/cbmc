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
/// the substring of `s2` starting at index `start_index` and ending
/// at index `end_index`.
///
/// If `start_index >= end_index`, the value returned is `s1`.
/// If `end_index > |s2|` and/or `start_index < 0`, the appended string will
/// be of length `end_index - start_index` and padded with non-deterministic
/// values.
///
/// These axioms are:
///   1. \f$end\_index > start\_index \Rightarrow |res| = |s_1| + end\_index -
///        start\_index
///     \f$
///   2. \f$end\_index \le start\_index \Rightarrow res = s_1 \f$
///   3. \f$\forall i<|s_1|. res[i]=s_1[i] \f$
///   4. \f$\forall i< end\_index - start\_index.\ res[i+|s_1|]
///        = s_2[start\_index+i]\f$
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
  binary_relation_exprt prem(end_index, ID_gt, start_index);

  exprt res_length=plus_exprt_with_overflow_check(
    s1.length(), minus_exprt(end_index, start_index));
  implies_exprt a1(prem, equal_exprt(res.length(), res_length));
  lemmas.push_back(a1);

  implies_exprt a2(not_exprt(prem), equal_exprt(res.length(), s1.length()));
  lemmas.push_back(a2);

  symbol_exprt idx=fresh_univ_index("QA_index_concat", res.length().type());
  string_constraintt a3(idx, s1.length(), equal_exprt(s1[idx], res[idx]));
  constraints.push_back(a3);

  symbol_exprt idx2=fresh_univ_index("QA_index_concat2", res.length().type());
  equal_exprt res_eq(
    res[plus_exprt(idx2, s1.length())], s2[plus_exprt(start_index, idx2)]);
  string_constraintt a4(idx2, minus_exprt(end_index, start_index), res_eq);
  constraints.push_back(a4);

  // We should have a enum type for the possible error codes
  return from_integer(0, res.length().type());
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
  const equal_exprt a1(
    res.length(), plus_exprt(s1.length(), from_integer(1, index_type)));
  lemmas.push_back(a1);

  symbol_exprt idx = fresh_univ_index("QA_index_concat_char", index_type);
  string_constraintt a2(idx, s1.length(), equal_exprt(s1[idx], res[idx]));
  constraints.push_back(a2);

  equal_exprt a3(res[s1.length()], c);
  lemmas.push_back(a3);

  // We should have a enum type for the possible error codes
  return from_integer(0, get_return_code_type());
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
