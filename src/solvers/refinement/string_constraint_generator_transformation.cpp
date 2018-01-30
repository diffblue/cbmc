/*******************************************************************\

Module: Generates string constraints for string transformations,
        that is, functions taking one string and returning another

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for string transformations, that is, functions
///   taking one string and returning another

#include <solvers/refinement/string_refinement_invariant.h>
#include <solvers/refinement/string_constraint_generator.h>
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
/// \param f: function application with arguments integer `|res|`, character
///           pointer `&res[0]`, refined_string `s1`, integer `k`
/// \return integer expressino equal to `0`
exprt string_constraint_generatort::add_axioms_for_set_length(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 4);
  const array_string_exprt res =
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const array_string_exprt s1 = get_string_expr(f.arguments()[2]);
  const exprt &k = f.arguments()[3];
  const typet &index_type = s1.length().type();
  const typet &char_type = s1.content().type().subtype();

  // We add axioms:
  // a1 : |res|=k
  // a2 : forall i<|res|. i < |s1|  ==> res[i] = s1[i]
  // a3 : forall i<|res|. i >= |s1| ==> res[i] = 0

  lemmas.push_back(res.axiom_for_has_length(k));

  symbol_exprt idx = fresh_univ_index("QA_index_set_length", index_type);
  string_constraintt a2(
    idx,
    res.length(),
    s1.axiom_for_length_gt(idx),
    equal_exprt(s1[idx], res[idx]));
  constraints.push_back(a2);

  symbol_exprt idx2 = fresh_univ_index("QA_index_set_length2", index_type);
  string_constraintt a3(
    idx2,
    res.length(),
    s1.axiom_for_length_le(idx2),
    equal_exprt(res[idx2], constant_char(0, char_type)));
  constraints.push_back(a3);

  return from_integer(0, signedbv_typet(32));
}

/// Substring of a string between two indices
///
/// \copybrief string_constraint_generatort::add_axioms_for_substring(
///   const array_string_exprt &res,
///   const array_string_exprt &str,
///   const exprt &start,
///   const exprt &end)
// NOLINTNEXTLINE
/// \link string_constraint_generatort::add_axioms_for_substring(const array_string_exprt &res, const array_string_exprt &str, const exprt &start, const exprt &end)
///   (More...) \endlink
/// \warning The specification may not be correct for the case where the string
/// is shorter than the end index
/// \todo Should return a integer different from zero when the string is shorter
///   tan the end index.
/// \param f: function application with arguments integer `|res|`, character
///           pointer `&res[0]`, refined_string `str`, integer `start`,
///           optional integer `end` with default value `|str|`.
/// \return integer expression which is different from 0 when there is an
///         exception to signal
exprt string_constraint_generatort::add_axioms_for_substring(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  PRECONDITION(args.size() == 4 || args.size() == 5);
  const array_string_exprt str = get_string_expr(args[2]);
  const array_string_exprt res = char_array_of_pointer(args[1], args[0]);
  const exprt &i = args[3];
  const exprt j = args.size() == 5 ? args[4] : str.length();
  return add_axioms_for_substring(res, str, i, j);
}

/// Add axioms ensuring that `res` corresponds to the substring of `str`
/// between indexes `start` and `end`.
///
/// These axioms are:
///   1. \f$ {\tt start} < {\tt end} \Rightarrow
///          |{\tt res}| = {\tt end} - {\tt start} \f$
///   2. \f$ {\tt start} \ge {\tt end} \Rightarrow |{\tt res}| = 0 \f$
///   3. \f$ |{\tt str}| > {\tt end} \f$
///   4. \f$ \forall i<|{\tt str}|.\ {\tt res}[i]={\tt str}[{\tt start}+i] \f$
/// \todo Should return code different from 0 if `|str| <= |end|` instead of
///       adding constraint 3.
/// \param res: array of characters expression
/// \param str: array of characters expression
/// \param start: integer expression
/// \param end: integer expression
/// \return integer expression equal to zero
exprt string_constraint_generatort::add_axioms_for_substring(
  const array_string_exprt &res,
  const array_string_exprt &str,
  const exprt &start,
  const exprt &end)
{
  const typet &index_type = str.length().type();
  PRECONDITION(start.type()==index_type);
  PRECONDITION(end.type()==index_type);

  // We add axioms:

  implies_exprt a1(
    binary_relation_exprt(start, ID_lt, end),
    res.axiom_for_has_length(minus_exprt(end, start)));
  lemmas.push_back(a1);

  exprt is_empty=res.axiom_for_has_length(from_integer(0, index_type));
  implies_exprt a2(binary_relation_exprt(start, ID_ge, end), is_empty);
  lemmas.push_back(a2);

  // Warning: check what to do if the string is not long enough
  lemmas.push_back(str.axiom_for_length_ge(end));

  symbol_exprt idx=fresh_univ_index("QA_index_substring", index_type);
  string_constraintt a4(idx,
                        res.length(),
                        equal_exprt(res[idx],
                        str[plus_exprt(start, idx)]));
  constraints.push_back(a4);
  return from_integer(0, signedbv_typet(32));
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
///           pointer `&res[0]`, refined_string `str`.
/// \return integer expression which is different from 0 when there is an
///         exception to signal
exprt string_constraint_generatort::add_axioms_for_trim(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 3);
  const array_string_exprt &str = get_string_expr(f.arguments()[2]);
  const array_string_exprt &res =
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const typet &index_type = str.length().type();
  const typet &char_type = str.content().type().subtype();
  const symbol_exprt idx = fresh_exist_index("index_trim", index_type);
  const exprt space_char = from_integer(' ', char_type);

  exprt a1=str.axiom_for_length_ge(
    plus_exprt_with_overflow_check(idx, res.length()));
  lemmas.push_back(a1);

  binary_relation_exprt a2(idx, ID_ge, from_integer(0, index_type));
  lemmas.push_back(a2);

  exprt a3=str.axiom_for_length_ge(idx);
  lemmas.push_back(a3);

  exprt a4=res.axiom_for_length_ge(
    from_integer(0, index_type));
  lemmas.push_back(a4);

  exprt a5 = res.axiom_for_length_le(str.length());
  lemmas.push_back(a5);

  symbol_exprt n=fresh_univ_index("QA_index_trim", index_type);
  binary_relation_exprt non_print(str[n], ID_le, space_char);
  string_constraintt a6(n, idx, non_print);
  constraints.push_back(a6);

  symbol_exprt n2=fresh_univ_index("QA_index_trim2", index_type);
  minus_exprt bound(str.length(), plus_exprt_with_overflow_check(idx,
                                                                 res.length()));
  binary_relation_exprt eqn2(
    str[plus_exprt(idx, plus_exprt(res.length(), n2))],
    ID_le,
    space_char);

  string_constraintt a7(n2, bound, eqn2);
  constraints.push_back(a7);

  symbol_exprt n3=fresh_univ_index("QA_index_trim3", index_type);
  equal_exprt eqn3(res[n3], str[plus_exprt(n3, idx)]);
  string_constraintt a8(n3, res.length(), eqn3);
  constraints.push_back(a8);

  minus_exprt index_before(
    plus_exprt_with_overflow_check(idx, res.length()),
      from_integer(1, index_type));
  binary_relation_exprt no_space_before(str[index_before], ID_gt, space_char);
  or_exprt a9(
    equal_exprt(idx, str.length()),
    and_exprt(
      binary_relation_exprt(str[idx], ID_gt, space_char),
      no_space_before));
  lemmas.push_back(a9);
  return from_integer(0, f.type());
}

/// Conversion of a string to lower case
///
/// Add axioms ensuring `res` corresponds to `str` in which uppercase characters
/// have been converted to lowercase.
/// These axioms are:
///   1. \f$ |{\tt res}| = |{\tt str}| \f$
///   2. \f$ \forall i<|{\tt str}|.\ {\tt is\_upper\_case}({\tt str}[i])?
///      {\tt res}[i]={\tt str}[i]+diff : {\tt res}[i]={\tt str}[i]
///      \land {\tt str}[i]<{\tt 0x100} \f$
///      where `diff` is the difference between lower case and upper case
///      characters: `diff = 'a'-'A' = 0x20`.
///
/// \param f: function application with arguments integer `|res|`, character
///           pointer `&res[0]`, refined_string `str`
/// \return integer expression which is different from `0` when there is an
///         exception to signal
exprt string_constraint_generatort::add_axioms_for_to_lower_case(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 3);
  const array_string_exprt res =
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const array_string_exprt str = get_string_expr(f.arguments()[2]);
  const refined_string_typet &ref_type =
    to_refined_string_type(f.arguments()[2].type());
  const typet &char_type=ref_type.get_char_type();
  const typet &index_type=ref_type.get_index_type();
  const exprt char_A=constant_char('A', char_type);
  const exprt char_Z=constant_char('Z', char_type);

  // \todo for now, only characters in Basic Latin and Latin-1 supplement
  // are supported (up to 0x100), we should add others using case mapping
  // information from the UnicodeData file.

  equal_exprt a1(res.length(), str.length());
  lemmas.push_back(a1);

  symbol_exprt idx=fresh_univ_index("QA_lower_case", index_type);
  exprt::operandst upper_case;
  // Characters between 'A' and 'Z' are upper-case
  upper_case.push_back(and_exprt(
    binary_relation_exprt(char_A, ID_le, str[idx]),
    binary_relation_exprt(str[idx], ID_le, char_Z)));

  // Characters between 0xc0 (latin capital A with grave)
  // and 0xd6 (latin capital O with diaeresis) are upper-case
  upper_case.push_back(and_exprt(
    binary_relation_exprt(from_integer(0xc0, char_type), ID_le, str[idx]),
    binary_relation_exprt(str[idx], ID_le, from_integer(0xd6, char_type))));

  // Characters between 0xd8 (latin capital O with stroke)
  // and 0xde (latin capital thorn) are upper-case
  upper_case.push_back(and_exprt(
    binary_relation_exprt(from_integer(0xd8, char_type), ID_le, str[idx]),
    binary_relation_exprt(str[idx], ID_le, from_integer(0xde, char_type))));

  exprt is_upper_case=disjunction(upper_case);

  // The difference between upper-case and lower-case for the basic latin and
  // latin-1 supplement is 0x20.
  exprt diff=from_integer(0x20, char_type);
  equal_exprt converted(res[idx], plus_exprt(str[idx], diff));
  and_exprt non_converted(
    equal_exprt(res[idx], str[idx]),
    binary_relation_exprt(str[idx], ID_lt, from_integer(0x100, char_type)));
  if_exprt conditional_convert(is_upper_case, converted, non_converted);

  string_constraintt a2(idx, res.length(), conditional_convert);
  constraints.push_back(a2);

  return from_integer(0, f.type());
}

/// Add axioms ensuring `res` corresponds to `str` in which lowercase characters
/// have been converted to uppercase.
///
/// These axioms are:
///   1. \f$ |{\tt res}| = |{\tt str}| \f$
///   2. \f$ \forall i<|{\tt str}|.\ 'a'\le {\tt str}[i]\le 'z'
///          \Rightarrow {\tt res}[i]={\tt str}[i]+'A'-'a' \f$
///   3. \f$ \forall i<|{\tt str}|.\ \lnot ('a'\le {\tt str}[i] \le 'z')
///          \Rightarrow {\tt res}[i]={\tt str}[i] \f$
/// Note that index expressions are only allowed in the body of universal
/// axioms, so we use a trivial premise and push our premise into the body.
///
/// \todo We can reduce the number of constraints by merging
///       constraints 2 and 3.
/// \param res: array of characters expression
/// \param str: array of characters expression
/// \return integer expression which is different from `0` when there is an
///         exception to signal
exprt string_constraint_generatort::add_axioms_for_to_upper_case(
  const array_string_exprt &res,
  const array_string_exprt &str)
{
  const typet &char_type = str.content().type().subtype();
  const typet &index_type = str.length().type();
  exprt char_a=constant_char('a', char_type);
  exprt char_A=constant_char('A', char_type);
  exprt char_z=constant_char('z', char_type);

  // \todo Add support for locales using case mapping information
  // from the UnicodeData file.

  equal_exprt a1(res.length(), str.length());
  lemmas.push_back(a1);

  symbol_exprt idx1=fresh_univ_index("QA_upper_case1", index_type);
  exprt is_lower_case=and_exprt(
    binary_relation_exprt(char_a, ID_le, str[idx1]),
    binary_relation_exprt(str[idx1], ID_le, char_z));
  minus_exprt diff(char_A, char_a);
  equal_exprt convert(res[idx1], plus_exprt(str[idx1], diff));
  implies_exprt body1(is_lower_case, convert);
  string_constraintt a2(idx1, res.length(), body1);
  constraints.push_back(a2);

  symbol_exprt idx2=fresh_univ_index("QA_upper_case2", index_type);
  exprt is_not_lower_case=not_exprt(and_exprt(
    binary_relation_exprt(char_a, ID_le, str[idx2]),
    binary_relation_exprt(str[idx2], ID_le, char_z)));
  equal_exprt eq(res[idx2], str[idx2]);
  implies_exprt body2(is_not_lower_case, eq);
  string_constraintt a3(idx2, res.length(), body2);
  constraints.push_back(a3);
  return from_integer(0, signedbv_typet(32));
}

/// Conversion of a string to upper case
///
// NOLINTNEXTLINE
/// \copybrief string_constraint_generatort::add_axioms_for_to_upper_case(const array_string_exprt&, const array_string_exprt&)
// NOLINTNEXTLINE
/// \link string_constraint_generatort::add_axioms_for_to_upper_case(const array_string_exprt &res, const array_string_exprt &str)
///   (More...) \endlink
/// \param f: function application with arguments integer `|res|`, character
///           pointer `&res[0]`, refined_string `str`
/// \return integer expression which is different from `0` when there is an
///         exception to signal
exprt string_constraint_generatort::add_axioms_for_to_upper_case(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 3);
  array_string_exprt res =
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  array_string_exprt str = get_string_expr(f.arguments()[2]);
  return add_axioms_for_to_upper_case(res, str);
}

/// Set a character to a specific value at an index of the string
///
/// Add axioms ensuring that the result `res` is similar to input string `str`
/// where the character at index `pos` is set to `char`.
/// These axioms are:
///   1. \f$ |{\tt res}| = |{\tt str}|\f$
///   2. \f$ {\tt res}[{\tt pos}]={\tt char}\f$
///   3. \f$ \forall i<|{\tt res}|.\ i \ne {\tt pos}
///          \Rightarrow {\tt res}[i] = {\tt str}[i]\f$
/// \param f: function application with arguments integer `|res|`, character
///           pointer `&res[0]`, refined_string `str`, integer `pos`,
///           and character `char`
/// \return an integer expression which is `1` when `pos` is out of bounds and
///         `0` otherwise
exprt string_constraint_generatort::add_axioms_for_char_set(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 5);
  const array_string_exprt str = get_string_expr(f.arguments()[2]);
  const array_string_exprt res =
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const exprt &position = f.arguments()[3];
  const exprt &character = f.arguments()[4];

  const binary_relation_exprt out_of_bounds(position, ID_ge, str.length());
  lemmas.push_back(equal_exprt(res.length(), str.length()));
  lemmas.push_back(equal_exprt(res[position], character));
  const symbol_exprt q = fresh_univ_index("QA_char_set", position.type());
  equal_exprt a3_body(res[q], str[q]);
  notequal_exprt a3_guard(q, position);
  constraints.push_back(
    string_constraintt(
      q, from_integer(0, q.type()), res.length(), a3_guard, a3_body));
  return if_exprt(
    out_of_bounds, from_integer(1, f.type()), from_integer(0, f.type()));
}

/// Convert two expressions to pair of chars
/// If both expressions are characters, return pair of them
/// If both expressions are 1-length strings, return first character of each
/// Otherwise return empty optional
/// \param expr1 First expression
/// \param expr2 Second expression
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
/// \param f: function application with arguments integer `|res|`, character
///           pointer `&res[0]`, refined_string `str`, character `old_char` and
///           character `new_char`
/// \return an integer expression equal to 0
exprt string_constraint_generatort::add_axioms_for_replace(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 5);
  array_string_exprt str = get_string_expr(f.arguments()[2]);
  array_string_exprt res =
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  if(
    const auto maybe_chars =
      to_char_pair(f.arguments()[3], f.arguments()[4], [this](const exprt &e) { // NOLINT
        return get_string_expr(e);
      }))
  {
    const auto old_char=maybe_chars->first;
    const auto new_char=maybe_chars->second;

    lemmas.push_back(equal_exprt(res.length(), str.length()));

    symbol_exprt qvar = fresh_univ_index("QA_replace", str.length().type());
    implies_exprt case1(
      equal_exprt(str[qvar], old_char),
      equal_exprt(res[qvar], new_char));
    implies_exprt case2(
      not_exprt(equal_exprt(str[qvar], old_char)),
      equal_exprt(res[qvar], str[qvar]));
    string_constraintt a2(qvar, res.length(), and_exprt(case1, case2));
    constraints.push_back(a2);
    return from_integer(0, f.type());
  }
  return from_integer(1, f.type());
}

/// add axioms corresponding to the StringBuilder.deleteCharAt java function
/// \param f: function application with two arguments, the first is a
///   string and the second is an index
/// \return an expression whose value is non null to signal an exception
exprt string_constraint_generatort::add_axioms_for_delete_char_at(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 4);
  const array_string_exprt res =
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const array_string_exprt str = get_string_expr(f.arguments()[2]);
  exprt index_one=from_integer(1, str.length().type());
  return add_axioms_for_delete(
    res,
    str,
    f.arguments()[3],
    plus_exprt_with_overflow_check(f.arguments()[3], index_one));
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
exprt string_constraint_generatort::add_axioms_for_delete(
  const array_string_exprt &res,
  const array_string_exprt &str,
  const exprt &start,
  const exprt &end)
{
  PRECONDITION(start.type()==str.length().type());
  PRECONDITION(end.type()==str.length().type());
  const typet &index_type = str.length().type();
  const typet &char_type = str.content().type().subtype();
  const array_string_exprt sub1 = fresh_string(index_type, char_type);
  const array_string_exprt sub2 = fresh_string(index_type, char_type);
  const exprt return_code1 = add_axioms_for_substring(
    sub1, str, from_integer(0, str.length().type()), start);
  const exprt return_code2 =
    add_axioms_for_substring(sub2, str, end, str.length());
  const exprt return_code3 = add_axioms_for_concat(res, sub1, sub2);
  return bitor_exprt(return_code1, bitor_exprt(return_code2, return_code3));
}

/// Remove a portion of a string
///
// NOLINTNEXTLINE
/// \copybrief string_constraint_generatort::add_axioms_for_delete(const array_string_exprt &res, const array_string_exprt &str, const exprt &start, const exprt &end)
// NOLINTNEXTLINE
/// \link string_constraint_generatort::add_axioms_for_delete(const array_string_exprt &res, const array_string_exprt &str, const exprt &start, const exprt &end)
///   (More...) \endlink
/// \param f: function application with arguments integer `|res|`, character
///           pointer `&res[0]`, refined_string `str`, integer `start`
///           and integer `end`
/// \return an integer expression whose value is different from 0 to signal
///   an exception
exprt string_constraint_generatort::add_axioms_for_delete(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 5);
  const array_string_exprt res =
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const array_string_exprt arg = get_string_expr(f.arguments()[2]);
  return add_axioms_for_delete(res, arg, f.arguments()[3], f.arguments()[4]);
}
