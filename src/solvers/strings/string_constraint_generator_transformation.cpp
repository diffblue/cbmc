/*******************************************************************\

Module: Generates string constraints for string transformations,
        that is, functions taking one string and returning another

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for string transformations, that is, functions
///   taking one string and returning another

#include "string_refinement_invariant.h"
#include "string_constraint_generator.h"

#include <util/arith_tools.h>

/// Reduce or extend a string to have the given length
///
/// Add axioms ensuring the returned string expression `res` has length `k`
/// and characters at position `i` in `res` are equal to the character at
/// position `i` in `s1` if `i` is smaller that the length of `s1`, otherwise
/// it is the null character `\u0000`.
///
/// These axioms are:
///   1. \f$ |{\tt res}|={\tt k} \f$
///   2. \f$ \forall i<|{\tt res}|.\ i < |s_1|
///          \Rightarrow {\tt res}[i] = s_1[i] \f$
///   3. \f$ \forall i<|{\tt res}|.\ i \ge |s_1|
///          \Rightarrow {\tt res}[i] = 0 \f$
/// \todo We can reduce the number of constraints by merging 2 and 3.
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with arguments integer `|res|`, character
///   pointer `&res[0]`, refined_string `s1`, integer `k`
/// \param array_pool: pool of arrays representing strings
/// \return integer expression equal to `0`
std::pair<exprt, string_constraintst> add_axioms_for_set_length(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  PRECONDITION(f.arguments().size() == 4);
  string_constraintst constraints;
  const array_string_exprt res =
    char_array_of_pointer(array_pool, f.arguments()[1], f.arguments()[0]);
  const array_string_exprt s1 = get_string_expr(array_pool, f.arguments()[2]);
  const exprt &k = f.arguments()[3];
  const typet &index_type = s1.length().type();
  const typet &char_type = s1.content().type().subtype();

  // We add axioms:
  // a1 : |res|=k
  // a2 : forall i< min(|s1|, k) .res[i] = s1[i]
  // a3 : forall |s1| <= i < |res|. res[i] = 0

  constraints.existential.push_back(length_eq(res, k));

  const symbol_exprt idx = fresh_symbol("QA_index_set_length", index_type);
  const string_constraintt a2(
    idx,
    zero_if_negative(minimum(s1.length(), k)),
    equal_exprt(s1[idx], res[idx]));
  constraints.universal.push_back(a2);

  symbol_exprt idx2 = fresh_symbol("QA_index_set_length2", index_type);
  string_constraintt a3(
    idx2,
    zero_if_negative(s1.length()),
    zero_if_negative(res.length()),
    equal_exprt(res[idx2], from_integer(0, char_type)));
  constraints.universal.push_back(a3);

  return {from_integer(0, get_return_code_type()), std::move(constraints)};
}

/// Substring of a string between two indices
///
// NOLINTNEXTLINE
/// \copybrief add_axioms_for_substring(symbol_generatort &fresh_symbol, const array_string_exprt &res, const array_string_exprt &str, const exprt &start, const exprt &end)
// NOLINTNEXTLINE
/// \link string_constraint_generatort::add_axioms_for_substring(symbol_generatort &fresh_symbol, const array_string_exprt &res, const array_string_exprt &str, const exprt &start, const exprt &end)
///   (More...) \endlink
/// \warning The specification may not be correct for the case where the string
/// is shorter than the end index
/// \todo Should return a integer different from zero when the string is shorter
///   tan the end index.
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with arguments integer `|res|`, character
///   pointer `&res[0]`, refined_string `str`, integer `start`, optional integer
///   `end` with default value `|str|`.
/// \param array_pool: pool of arrays representing strings
/// \return integer expression which is different from 0 when there is an
///   exception to signal
std::pair<exprt, string_constraintst> add_axioms_for_substring(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  const function_application_exprt::argumentst &args=f.arguments();
  PRECONDITION(args.size() == 4 || args.size() == 5);
  const array_string_exprt str = get_string_expr(array_pool, args[2]);
  const array_string_exprt res =
    char_array_of_pointer(array_pool, args[1], args[0]);
  const exprt &i = args[3];
  const exprt j = args.size() == 5 ? args[4] : str.length();
  return add_axioms_for_substring(fresh_symbol, res, str, i, j);
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
/// \param fresh_symbol: generator of fresh symbols
/// \param res: array of characters expression
/// \param str: array of characters expression
/// \param start: integer expression
/// \param end: integer expression
/// \return integer expression equal to zero
std::pair<exprt, string_constraintst> add_axioms_for_substring(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const array_string_exprt &str,
  const exprt &start,
  const exprt &end)
{
  const typet &index_type = str.length().type();
  PRECONDITION(start.type()==index_type);
  PRECONDITION(end.type()==index_type);

  string_constraintst constraints;
  const exprt start1 = maximum(start, from_integer(0, start.type()));
  const exprt end1 = maximum(minimum(end, str.length()), start1);

  // Axiom 1.
  constraints.existential.push_back(
    equal_exprt(res.length(), minus_exprt(end1, start1)));

  // Axiom 2.
  constraints.universal.push_back([&] {
    const symbol_exprt idx = fresh_symbol("QA_index_substring", index_type);
    return string_constraintt(
      idx,
      zero_if_negative(res.length()),
      equal_exprt(res[idx], str[plus_exprt(start1, idx)]));
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
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with arguments integer `|res|`, character
///   pointer `&res[0]`, refined_string `str`.
/// \param array_pool: pool of arrays representing strings
/// \return integer expression which is different from 0 when there is an
///   exception to signal
std::pair<exprt, string_constraintst> add_axioms_for_trim(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  PRECONDITION(f.arguments().size() == 3);
  string_constraintst constraints;
  const array_string_exprt &str = get_string_expr(array_pool, f.arguments()[2]);
  const array_string_exprt &res =
    char_array_of_pointer(array_pool, f.arguments()[1], f.arguments()[0]);
  const typet &index_type = str.length().type();
  const typet &char_type = str.content().type().subtype();
  const symbol_exprt idx = fresh_symbol("index_trim", index_type);
  const exprt space_char = from_integer(' ', char_type);

  // Axiom 1.
  constraints.existential.push_back(
    length_ge(str, plus_exprt(idx, res.length())));

  binary_relation_exprt a2(idx, ID_ge, from_integer(0, index_type));
  constraints.existential.push_back(a2);

  const exprt a3 = length_ge(str, idx);
  constraints.existential.push_back(a3);

  const exprt a4 = length_ge(res, from_integer(0, index_type));
  constraints.existential.push_back(a4);

  const exprt a5 = length_le(res, str.length());
  constraints.existential.push_back(a5);

  symbol_exprt n = fresh_symbol("QA_index_trim", index_type);
  binary_relation_exprt non_print(str[n], ID_le, space_char);
  string_constraintt a6(n, zero_if_negative(idx), non_print);
  constraints.universal.push_back(a6);

  // Axiom 7.
  constraints.universal.push_back([&] {
    const symbol_exprt n2 = fresh_symbol("QA_index_trim2", index_type);
    const minus_exprt bound(minus_exprt(str.length(), idx), res.length());
    const binary_relation_exprt eqn2(
      str[plus_exprt(idx, plus_exprt(res.length(), n2))], ID_le, space_char);
    return string_constraintt(n2, zero_if_negative(bound), eqn2);
  }());

  symbol_exprt n3 = fresh_symbol("QA_index_trim3", index_type);
  equal_exprt eqn3(res[n3], str[plus_exprt(n3, idx)]);
  string_constraintt a8(n3, zero_if_negative(res.length()), eqn3);
  constraints.universal.push_back(a8);

  // Axiom 9.
  constraints.existential.push_back([&] {
    const plus_exprt index_before(
      idx, minus_exprt(res.length(), from_integer(1, index_type)));
    const binary_relation_exprt no_space_before(
      str[index_before], ID_gt, space_char);
    return or_exprt(
      equal_exprt(idx, str.length()),
      and_exprt(
        binary_relation_exprt(str[idx], ID_gt, space_char), no_space_before));
  }());
  return {from_integer(0, f.type()), constraints};
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
/// \return Optional pair of two expressions
static optionalt<std::pair<exprt, exprt>> to_char_pair(
  exprt expr1,
  exprt expr2,
  std::function<array_string_exprt(const exprt &)> get_string_expr)
{
  if((expr1.type().id()==ID_unsignedbv
      || expr1.type().id()==ID_char)
     && (expr2.type().id()==ID_char
         || expr2.type().id()==ID_unsignedbv))
    return std::make_pair(expr1, expr2);
  const auto expr1_str = get_string_expr(expr1);
  const auto expr2_str = get_string_expr(expr2);
  const auto expr1_length = numeric_cast<std::size_t>(expr1_str.length());
  const auto expr2_length = numeric_cast<std::size_t>(expr2_str.length());
  if(expr1_length && expr2_length && *expr1_length==1 && *expr2_length==1)
    return std::make_pair(exprt(expr1_str[0]), exprt(expr2_str[0]));
  return { };
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
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with arguments integer `|res|`, character
///   pointer `&res[0]`, refined_string `str`, character `old_char` and
///   character `new_char`
/// \param array_pool: pool of arrays representing strings
/// \return an integer expression equal to 0
std::pair<exprt, string_constraintst> add_axioms_for_replace(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  PRECONDITION(f.arguments().size() == 5);
  string_constraintst constraints;
  array_string_exprt str = get_string_expr(array_pool, f.arguments()[2]);
  array_string_exprt res =
    char_array_of_pointer(array_pool, f.arguments()[1], f.arguments()[0]);
  if(
    const auto maybe_chars =
      to_char_pair(f.arguments()[3], f.arguments()[4], [&](const exprt &e) {
        return get_string_expr(array_pool, e);
      }))
  {
    const auto old_char=maybe_chars->first;
    const auto new_char=maybe_chars->second;

    constraints.existential.push_back(equal_exprt(res.length(), str.length()));

    symbol_exprt qvar = fresh_symbol("QA_replace", str.length().type());
    implies_exprt case1(
      equal_exprt(str[qvar], old_char),
      equal_exprt(res[qvar], new_char));
    implies_exprt case2(
      not_exprt(equal_exprt(str[qvar], old_char)),
      equal_exprt(res[qvar], str[qvar]));
    string_constraintt a2(
      qvar, zero_if_negative(res.length()), and_exprt(case1, case2));
    constraints.universal.push_back(a2);
    return {from_integer(0, f.type()), std::move(constraints)};
  }
  return {from_integer(1, f.type()), std::move(constraints)};
}

/// add axioms corresponding to the StringBuilder.deleteCharAt java function
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with two arguments, the first is a
///   string and the second is an index
/// \param array_pool: pool of arrays representing strings
/// \return an expression whose value is non null to signal an exception
std::pair<exprt, string_constraintst> add_axioms_for_delete_char_at(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  PRECONDITION(f.arguments().size() == 4);
  const array_string_exprt res =
    char_array_of_pointer(array_pool, f.arguments()[1], f.arguments()[0]);
  const array_string_exprt str = get_string_expr(array_pool, f.arguments()[2]);
  exprt index_one=from_integer(1, str.length().type());
  return add_axioms_for_delete(
    fresh_symbol,
    res,
    str,
    f.arguments()[3],
    plus_exprt(f.arguments()[3], index_one),
    array_pool);
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
/// \param fresh_symbol: generator of fresh symbols
/// \param res: array of characters expression
/// \param str: array of characters expression
/// \param start: integer expression
/// \param end: integer expression
/// \param array_pool: pool of arrays representing strings
/// \return integer expression different from zero to signal an exception
std::pair<exprt, string_constraintst> add_axioms_for_delete(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const array_string_exprt &str,
  const exprt &start,
  const exprt &end,
  array_poolt &array_pool)
{
  PRECONDITION(start.type()==str.length().type());
  PRECONDITION(end.type()==str.length().type());
  const typet &index_type = str.length().type();
  const typet &char_type = str.content().type().subtype();
  const array_string_exprt sub1 =
    array_pool.fresh_string(index_type, char_type);
  const array_string_exprt sub2 =
    array_pool.fresh_string(index_type, char_type);
  return combine_results(
    add_axioms_for_substring(
      fresh_symbol, sub1, str, from_integer(0, str.length().type()), start),
    combine_results(
      add_axioms_for_substring(fresh_symbol, sub2, str, end, str.length()),
      add_axioms_for_concat(fresh_symbol, res, sub1, sub2)));
}

/// Remove a portion of a string
///
// NOLINTNEXTLINE
/// \copybrief add_axioms_for_delete(symbol_generatort &fresh_symbol, const array_string_exprt &res, const array_string_exprt &str, const exprt &start, const exprt &end, array_poolt &array_pool)
// NOLINTNEXTLINE
/// \link add_axioms_for_delete(symbol_generatort &fresh_symbol,const array_string_exprt &res, const array_string_exprt &str, const exprt &start, const exprt &end, array_poolt &array_pool)
///   (More...) \endlink
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with arguments integer `|res|`, character
///   pointer `&res[0]`, refined_string `str`, integer `start` and integer `end`
/// \param array_pool: pool of arrays representing strings
/// \return an integer expression whose value is different from 0 to signal
///   an exception
std::pair<exprt, string_constraintst> add_axioms_for_delete(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  PRECONDITION(f.arguments().size() == 5);
  const array_string_exprt res =
    char_array_of_pointer(array_pool, f.arguments()[1], f.arguments()[0]);
  const array_string_exprt arg = get_string_expr(array_pool, f.arguments()[2]);
  return add_axioms_for_delete(
    fresh_symbol, res, arg, f.arguments()[3], f.arguments()[4], array_pool);
}
