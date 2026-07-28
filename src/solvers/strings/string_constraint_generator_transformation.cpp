/*******************************************************************\

Module: Generates string constraints for string transformations,
        that is, functions taking one string and returning another

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for string transformations, that is, functions
///   taking one string and returning another

#include "string_constraint_generator.h"

#include <util/arith_tools.h>
#include <util/mathematical_expr.h>

/// Reduce or extend a string to have the given length
///
/// Add axioms ensuring the returned string expression `res` has length
/// `max(k, 0)` and characters at position `i` in `res` are equal to the
/// character at position `i` in `s1` if `i` is smaller that the length of `s1`,
/// otherwise it is the null character `\u0000`.
/// Note this means if `k` is negative then the string is truncated to length 0;
/// in practice a wrapper function will usually handle this case.
///
/// These axioms are:
///   1. \f$ |{\tt res}|={\tt k} \f$
///   2. \f$ \forall i<|{\tt res}|.\ i < |s_1|
///          \Rightarrow {\tt res}[i] = s_1[i] \f$
///   3. \f$ \forall i<|{\tt res}|.\ i \ge |s_1|
///          \Rightarrow {\tt res}[i] = 0 \f$
/// \todo We can reduce the number of constraints by merging 2 and 3.
/// \param f: function application with arguments integer `|res|`, character
///   pointer `&res[0]`, refined_string `s1`, integer `k`
/// \return integer expression equal to `0`
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_set_length(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 4);
  string_constraintst constraints;
  const array_string_exprt res =
    array_pool.find(f.arguments()[1], f.arguments()[0]);
  const array_string_exprt s1 = get_string_expr(array_pool, f.arguments()[2]);
  const exprt &k = f.arguments()[3];
  const typet &index_type = s1.length_type();
  const typet &char_type = to_type_with_subtype(s1.content().type()).subtype();

  // We add axioms:
  // a1 : |res|=max(k, 0)
  // a2 : forall i< min(|s1|, k) .res[i] = s1[i]
  // a3 : forall |s1| <= i < |res|. res[i] = 0

  constraints.existential.push_back(
    equal_to(array_pool.get_or_create_length(res), zero_if_negative(k)));

  const symbol_exprt idx = fresh_symbol("QA_index_set_length", index_type);
  const string_constraintt a2(
    idx,
    zero_if_negative(minimum(array_pool.get_or_create_length(s1), k)),
    equal_exprt(s1[idx], res[idx]),
    message_handler);
  constraints.universal.push_back(a2);

  symbol_exprt idx2 = fresh_symbol("QA_index_set_length2", index_type);
  string_constraintt a3(
    idx2,
    zero_if_negative(array_pool.get_or_create_length(s1)),
    zero_if_negative(array_pool.get_or_create_length(res)),
    equal_exprt(res[idx2], from_integer(0, char_type)),
    message_handler);
  constraints.universal.push_back(a3);

  return {from_integer(0, get_return_code_type()), std::move(constraints)};
}

/// Substring of a string between two indices
///
// NOLINTNEXTLINE
/// \copybrief add_axioms_for_substring(const array_string_exprt &res, const array_string_exprt &str, const exprt &start, const exprt &end)
// NOLINTNEXTLINE
/// \link string_constraint_generatort::add_axioms_for_substring(const array_string_exprt &res, const array_string_exprt &str, const exprt &start, const exprt &end)
///   (More...) \endlink
/// \warning The specification may not be correct for the case where the string
/// is shorter than the end index
/// \todo Should return a integer different from zero when the string is shorter
///   tan the end index.
/// \param f: function application with arguments integer `|res|`, character
///   pointer `&res[0]`, refined_string `str`, integer `start`, optional integer
///   `end` with default value `|str|`.
/// \return integer expression which is different from 0 when there is an
///   exception to signal
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_substring(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args = f.arguments();
  PRECONDITION(args.size() == 4 || args.size() == 5);
  const array_string_exprt str = get_string_expr(array_pool, args[2]);
  const array_string_exprt res = array_pool.find(args[1], args[0]);
  const exprt &i = args[3];
  const exprt j =
    args.size() == 5 ? args[4] : array_pool.get_or_create_length(str);
  return add_axioms_for_substring(res, str, i, j);
}

/// Add axioms ensuring that `res` corresponds to the substring of `str`
/// between indexes `start' = max(start, 0)` and
/// `end' = max(min(end, |str|), start')`.
///
/// These axioms are:
///   1. \f$ |{\tt res}| = end' - start' \f$
///   2. \f$ \forall i<|{\tt res}|.\ {\tt res}[i]={\tt str}[{\tt start'}+i] \f$
/// \todo Should return code different from 0 if `start' != start` or
///       `end' != end`
/// \param res: array of characters expression
/// \param str: array of characters expression
/// \param start: integer expression
/// \param end: integer expression
/// \return integer expression equal to zero
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_substring(
  const array_string_exprt &res,
  const array_string_exprt &str,
  const exprt &start,
  const exprt &end)
{
  const typet &index_type = str.length_type();
  PRECONDITION(start.type() == index_type);
  PRECONDITION(end.type() == index_type);

  string_constraintst constraints;
  const exprt start1 = maximum(start, from_integer(0, start.type()));
  const exprt end1 =
    maximum(minimum(end, array_pool.get_or_create_length(str)), start1);

  // Axiom 1.
  constraints.existential.push_back(equal_exprt(
    array_pool.get_or_create_length(res), minus_exprt(end1, start1)));

  // Axiom 2.
  constraints.universal.push_back([&] {
    const symbol_exprt idx = fresh_symbol("QA_index_substring", index_type);
    return string_constraintt(
      idx,
      zero_if_negative(array_pool.get_or_create_length(res)),
      equal_exprt(res[idx], str[plus_exprt(start1, idx)]),
      message_handler);
  }());

  return {from_integer(0, get_return_code_type()), std::move(constraints)};
}

/// Remove leading and trailing whitespaces
///
/// Add axioms ensuring `res` corresponds to `str` from which leading and
/// trailing whitespaces have been removed.
/// Are considered whitespaces, characters whose ascii code are smaller than
/// that of ' ' (space).
///
/// These axioms are:
///   1. \f$ idx + |{\tt res}| \le |{\tt str}| \f$ where `idx` represents
///      the index of the first non-space character.
///   2. \f$ idx \ge 0 \f$
///   3. \f$ |{\tt str}| \ge idx \f$
///   4. \f$ |{\tt res}| \ge 0 \f$
///   5. \f$ |{\tt res}| \le |{\tt str}| \f$
///        (this is necessary to prevent exceeding the biggest integer)
///   6. \f$ \forall n<m.\ {\tt str}[n] \le \lq~\rq \f$
///   7. \f$ \forall n<|{\tt str}|-m-|{\tt res}|.\ {\tt str}[m+|{\tt res}|+n]
///          \le \lq~\rq \f$
///   8. \f$ \forall n<|{\tt res}|.\ {\tt str}[idx+n]={\tt res}[n] \f$
///   9. \f$ (s[m]>{\tt \lq~\rq} \land s[m+|{\tt res}|-1]>{\tt \lq~\rq})
///          \lor m=|{\tt res}| \f$
/// \note Some of the constraints among 1, 2, 3, 4 and 5 seems to be redundant
/// \param f: function application with arguments integer `|res|`, character
///   pointer `&res[0]`, refined_string `str`.
/// \return integer expression which is different from 0 when there is an
///   exception to signal
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_trim(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 3);
  const array_string_exprt &str = get_string_expr(array_pool, f.arguments()[2]);
  const array_string_exprt &res =
    array_pool.find(f.arguments()[1], f.arguments()[0]);
  const typet &char_type = to_type_with_subtype(str.content().type()).subtype();
  const exprt space_char = from_integer(' ', char_type);
  // Java trim: strip characters <= ' ' from both ends.
  return add_axioms_for_strip(
    str,
    res,
    [&](const exprt &c) -> exprt
    { return binary_relation_exprt(c, ID_le, space_char); },
    true,
    true,
    f.type());
}

/// Generic parameterised strip (shared by Java trim and Python strip): remove
/// a maximal run of `is_strippable` characters from the front (if
/// `strip_front`) and/or back (if `strip_back`) of `str`, producing `res`.
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_strip(
  const array_string_exprt &str,
  const array_string_exprt &res,
  const std::function<exprt(const exprt &)> &is_strippable,
  bool strip_front,
  bool strip_back,
  const typet &result_type)
{
  string_constraintst constraints;
  const typet &index_type = str.length_type();
  const symbol_exprt idx = fresh_symbol("index_strip", index_type);
  const exprt str_len = array_pool.get_or_create_length(str);
  const exprt res_len = array_pool.get_or_create_length(res);

  constraints.existential.push_back(
    greater_or_equal_to(str_len, plus_exprt(idx, res_len)));
  constraints.existential.push_back(
    binary_relation_exprt(idx, ID_ge, from_integer(0, index_type)));
  constraints.existential.push_back(greater_or_equal_to(str_len, idx));
  constraints.existential.push_back(
    greater_or_equal_to(res_len, from_integer(0, index_type)));
  constraints.existential.push_back(less_than_or_equal_to(res_len, str_len));

  if(!strip_front)
    constraints.existential.push_back(
      equal_exprt(idx, from_integer(0, index_type)));
  if(!strip_back)
    constraints.existential.push_back(
      equal_exprt(res_len, minus_exprt(str_len, idx)));

  // res[n] == str[n + idx] for n < |res| (result is the kept middle slice).
  {
    const symbol_exprt n = fresh_symbol("QA_strip_copy", index_type);
    constraints.universal.push_back(string_constraintt(
      n,
      zero_if_negative(res_len),
      equal_exprt(res[n], str[plus_exprt(n, idx)]),
      message_handler));
  }
  // Removed front characters [0, idx) are strippable.
  if(strip_front)
  {
    const symbol_exprt n = fresh_symbol("QA_strip_front", index_type);
    constraints.universal.push_back(string_constraintt(
      n, zero_if_negative(idx), is_strippable(str[n]), message_handler));
  }
  // Removed trailing characters [idx+|res|, |str|) are strippable.
  if(strip_back)
  {
    const symbol_exprt n = fresh_symbol("QA_strip_back", index_type);
    const exprt bound = minus_exprt(minus_exprt(str_len, idx), res_len);
    constraints.universal.push_back(string_constraintt(
      n,
      zero_if_negative(bound),
      is_strippable(str[plus_exprt(idx, plus_exprt(res_len, n))]),
      message_handler));
  }

  // Maximality: either the result is empty (idx == |str|), or the kept
  // boundary characters are non-strippable (so all leading/trailing
  // strippable characters were removed).
  exprt non_strip = static_cast<exprt>(true_exprt{});
  if(strip_front)
    non_strip = and_exprt(non_strip, not_exprt(is_strippable(str[idx])));
  if(strip_back)
  {
    const exprt last =
      minus_exprt(plus_exprt(idx, res_len), from_integer(1, index_type));
    non_strip = and_exprt(non_strip, not_exprt(is_strippable(str[last])));
  }
  constraints.existential.push_back(
    or_exprt(equal_exprt(idx, str_len), non_strip));

  return {from_integer(0, result_type), std::move(constraints)};
}

/// Convert two expressions to pair of chars
/// If both expressions are characters, return pair of them
/// If both expressions are 1-length strings, return first character of each
/// Otherwise return empty optional
/// \param expr1: First expression
/// \param expr2: Second expression
/// \param get_string_expr: Function that yields an array_string_exprt
///   corresponding to either `expr1` or `expr2`, for the case where they are
///   not primitive chars.
/// \param array_pool: pool of arrays representing strings
/// \return Optional pair of two expressions
static std::optional<std::pair<exprt, exprt>> to_char_pair(
  exprt expr1,
  exprt expr2,
  std::function<array_string_exprt(const exprt &)> get_string_expr,
  array_poolt &array_pool)
{
  if(
    (expr1.type().id() == ID_unsignedbv || expr1.type().id() == ID_char) &&
    (expr2.type().id() == ID_char || expr2.type().id() == ID_unsignedbv))
    return std::make_pair(expr1, expr2);
  const auto expr1_str = get_string_expr(expr1);
  const auto expr2_str = get_string_expr(expr2);
  const auto expr1_length =
    numeric_cast<std::size_t>(array_pool.get_or_create_length(expr1_str));
  const auto expr2_length =
    numeric_cast<std::size_t>(array_pool.get_or_create_length(expr2_str));
  if(expr1_length && expr2_length && *expr1_length == 1 && *expr2_length == 1)
    return std::make_pair(exprt(expr1_str[0]), exprt(expr2_str[0]));
  return {};
}

/// Replace a character by another in a string
///
/// Add axioms ensuring that `res` corresponds to `str` where occurences of
/// `old_char` have been replaced by `new_char`.
/// These axioms are:
///   1. \f$ |{\tt res}| = |{\tt str}| \f$
///   2. \f$ \forall i \in 0, |{\tt res}|)
///          .\ {\tt str}[i]={\tt old\_char}
///          \Rightarrow {\tt res}[i]={\tt new\_char}
///          \land {\tt str}[i]\ne {\tt old\_char}
///          \Rightarrow {\tt res}[i]={\tt str}[i] \f$
/// Only supports String.replace(char, char) and
/// String.replace(String, String) for single-character strings
/// Returns original string in every other case (that behaviour is to
/// be fixed in the future)
/// \param f: function application with arguments integer `|res|`, character
///   pointer `&res[0]`, refined_string `str`, character `old_char` and
///   character `new_char`
/// \return an integer expression equal to 0
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_replace(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 5);
  string_constraintst constraints;
  array_string_exprt str = get_string_expr(array_pool, f.arguments()[2]);
  array_string_exprt res = array_pool.find(f.arguments()[1], f.arguments()[0]);
  if(
    const auto maybe_chars = to_char_pair(
      f.arguments()[3],
      f.arguments()[4],
      [&](const exprt &e) { return get_string_expr(array_pool, e); },
      array_pool))
  {
    const auto old_char = maybe_chars->first;
    const auto new_char = maybe_chars->second;

    constraints.existential.push_back(equal_exprt(
      array_pool.get_or_create_length(res),
      array_pool.get_or_create_length(str)));

    symbol_exprt qvar = fresh_symbol("QA_replace", str.length_type());
    implies_exprt case1(
      equal_exprt(str[qvar], old_char), equal_exprt(res[qvar], new_char));
    implies_exprt case2(
      not_exprt(equal_exprt(str[qvar], old_char)),
      equal_exprt(res[qvar], str[qvar]));
    string_constraintt a2(
      qvar,
      zero_if_negative(array_pool.get_or_create_length(res)),
      and_exprt(case1, case2),
      message_handler);
    constraints.universal.push_back(a2);
    return {from_integer(0, f.type()), std::move(constraints)};
  }
  return {from_integer(1, f.type()), std::move(constraints)};
}

/// add axioms corresponding to the StringBuilder.deleteCharAt java function
/// \param f: function application with two arguments, the first is a
///   string and the second is an index
/// \return an expression whose value is non null to signal an exception
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_delete_char_at(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 4);
  const array_string_exprt res =
    array_pool.find(f.arguments()[1], f.arguments()[0]);
  const array_string_exprt str = get_string_expr(array_pool, f.arguments()[2]);
  exprt index_one = from_integer(1, str.length_type());
  return add_axioms_for_delete(
    res, str, f.arguments()[3], plus_exprt(f.arguments()[3], index_one));
}

/// Add axioms stating that `res` corresponds to the input `str`
/// where we removed characters between the positions `start` (included) and
/// `end` (not included).
///
/// These axioms are the same as would be generated for:
/// `concat(substring(str, 0, start), substring(end, |str|))`
/// (see \ref add_axioms_for_substring and \ref add_axioms_for_concat_substr).
/// \todo Should use add_axioms_for_concat_substr instead
///       of add_axioms_for_concat
/// \param res: array of characters expression
/// \param str: array of characters expression
/// \param start: integer expression
/// \param end: integer expression
/// \return integer expression different from zero to signal an exception
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_delete(
  const array_string_exprt &res,
  const array_string_exprt &str,
  const exprt &start,
  const exprt &end)
{
  PRECONDITION(start.type() == str.length_type());
  PRECONDITION(end.type() == str.length_type());
  const typet &index_type = str.length_type();
  const typet &char_type = to_type_with_subtype(str.content().type()).subtype();
  const array_string_exprt sub1 =
    array_pool.fresh_string(index_type, char_type);
  const array_string_exprt sub2 =
    array_pool.fresh_string(index_type, char_type);
  return combine_results(
    add_axioms_for_substring(
      sub1, str, from_integer(0, str.length_type()), start),
    combine_results(
      add_axioms_for_substring(
        sub2, str, end, array_pool.get_or_create_length(str)),
      add_axioms_for_concat(res, sub1, sub2)));
}

/// Remove a portion of a string
///
// NOLINTNEXTLINE
/// \copybrief add_axioms_for_delete(const array_string_exprt &res, const array_string_exprt &str, const exprt &start, const exprt &end)
// NOLINTNEXTLINE
/// \link add_axioms_for_delete(const array_string_exprt &res, const array_string_exprt &str, const exprt &start, const exprt &end)
///   (More...) \endlink
/// \param f: function application with arguments integer `|res|`, character
///   pointer `&res[0]`, refined_string `str`, integer `start` and integer `end`
/// \return an integer expression whose value is different from 0 to signal
///   an exception
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_delete(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 5);
  const array_string_exprt res =
    array_pool.find(f.arguments()[1], f.arguments()[0]);
  const array_string_exprt arg = get_string_expr(array_pool, f.arguments()[2]);
  return add_axioms_for_delete(res, arg, f.arguments()[3], f.arguments()[4]);
}
