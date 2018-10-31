/*******************************************************************\

Module: Generates string constraints for function comparing strings,
        such as: equals, equalsIgnoreCase, compareTo, hashCode, intern

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for function comparing strings, such as:
///   equals, equalsIgnoreCase, compareTo, hashCode, intern

#include <solvers/refinement/string_constraint_generator.h>
#include <util/deprecate.h>

/// Equality of the content of two strings
///
/// Add axioms stating that the result is true exactly when the strings
/// represented by the arguments are equal.
/// These axioms are:
///   1. \f$ eq \Rightarrow |s_1|=|s_2|\f$
///   2. \f$ \forall i<|s_1|.\ eq \Rightarrow s_1[i]=s_2[i] \f$
///   3. \f$ \lnot eq \Rightarrow (|s_1| \ne |s_2| \land witness=-1)
///          \lor (0 \le witness<|s_1| \land s_1[witness] \ne s_2[witness]) \f$
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with arguments refined_string `s1` and
///           refined_string `s2`
/// \param pool: pool of arrays representing strings
/// \return Boolean expression `eq`
std::pair<exprt, string_constraintst> add_axioms_for_equals(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &pool)
{
  PRECONDITION(f.type()==bool_typet() || f.type().id()==ID_c_bool);
  PRECONDITION(f.arguments().size() == 2);

  string_constraintst constraints;
  array_string_exprt s1 = get_string_expr(pool, f.arguments()[0]);
  array_string_exprt s2 = get_string_expr(pool, f.arguments()[1]);
  symbol_exprt eq = fresh_symbol("equal");
  typecast_exprt tc_eq(eq, f.type());

  typet index_type=s1.length().type();

  // Axiom 1.
  constraints.existential.push_back(
    implies_exprt(eq, equal_exprt(s1.length(), s2.length())));

  // Axiom 2.
  constraints.universal.push_back([&] {
    const symbol_exprt qvar = fresh_symbol("QA_equal", index_type);
    return string_constraintt(
      qvar,
      zero_if_negative(s1.length()),
      implies_exprt(eq, equal_exprt(s1[qvar], s2[qvar])));
  }());

  // Axiom 3.
  constraints.existential.push_back([&] {
    const symbol_exprt witness = fresh_symbol("witness_unequal", index_type);
    const exprt zero = from_integer(0, index_type);
    const and_exprt bound_witness(
      binary_relation_exprt(witness, ID_lt, s1.length()),
      binary_relation_exprt(witness, ID_ge, zero));
    const and_exprt witnessing(
      bound_witness, notequal_exprt(s1[witness], s2[witness]));
    const and_exprt diff_length(
      notequal_exprt(s1.length(), s2.length()),
      equal_exprt(witness, from_integer(-1, index_type)));
    return implies_exprt(not_exprt(eq), or_exprt(diff_length, witnessing));
  }());

  return {tc_eq, std::move(constraints)};
}

/// Returns an expression which is true when the two given characters are equal
/// when ignoring case for ASCII
/// \todo The extra constant character arguments are not needed.
/// \param char1: character expression
/// \param char2: character expression
/// \param char_a: constant character 'a'
/// \param char_A: constant character 'A'
/// \param char_Z: constant character 'Z'
/// \return a expression of Boolean type
static exprt character_equals_ignore_case(
  const exprt &char1,
  const exprt &char2,
  const exprt &char_a,
  const exprt &char_A,
  const exprt &char_Z)
{
  const and_exprt is_upper_case_1(
    binary_relation_exprt(char_A, ID_le, char1),
    binary_relation_exprt(char1, ID_le, char_Z));
  const and_exprt is_upper_case_2(
    binary_relation_exprt(char_A, ID_le, char2),
    binary_relation_exprt(char2, ID_le, char_Z));

  // Three possibilities:
  // p1 : char1=char2
  // p2 : (is_up1&&'a'-'A'+char1=char2)
  // p3 : (is_up2&&'a'-'A'+char2=char1)
  const equal_exprt p1(char1, char2);
  const minus_exprt diff(char_a, char_A);

  // Overflow is not a problem here because is_upper_case conditions
  // ensure that we are within a safe range.
  const exprt p2 =
    and_exprt(is_upper_case_1, equal_exprt(plus_exprt(diff, char1), char2));
  const exprt p3 =
    and_exprt(is_upper_case_2, equal_exprt(plus_exprt(diff, char2), char1));
  return or_exprt(p1, p2, p3);
}

/// Equality of the content ignoring case of characters
///
/// Add axioms ensuring the result is true when the two strings
/// are equal if case is ignored.
/// These axioms are:
///   1. \f$ eq \Rightarrow |s_1|=|s_2|\f$
///   2. \f$ \forall i \in [0, |s_1|).
///          \ eq \Rightarrow {\tt equal\_ignore\_case}(s_1[i],s_2[i]) \f$
///   3. \f$ \lnot eq \Rightarrow |s_1| \ne |s_2| \lor (0 \le witness<|s_1|
///          \land\lnot {\tt equal\_ignore\_case}(s_1[witness],s_2[witness]) \f$
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with arguments refined_string `s1` and
///           refined_string `s2`
/// \param pool: pool of arrays representing strings
/// \return Boolean expression `eq`
std::pair<exprt, string_constraintst> add_axioms_for_equals_ignore_case(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &pool)
{
  PRECONDITION(f.type()==bool_typet() || f.type().id()==ID_c_bool);
  PRECONDITION(f.arguments().size() == 2);
  string_constraintst constraints;
  const symbol_exprt eq = fresh_symbol("equal_ignore_case");
  const array_string_exprt s1 = get_string_expr(pool, f.arguments()[0]);
  const array_string_exprt s2 = get_string_expr(pool, f.arguments()[1]);
  const typet char_type = s1.content().type().subtype();
  const exprt char_a = from_integer('a', char_type);
  const exprt char_A = from_integer('A', char_type);
  const exprt char_Z = from_integer('Z', char_type);
  const typet index_type = s1.length().type();

  const implies_exprt a1(eq, equal_exprt(s1.length(), s2.length()));
  constraints.existential.push_back(a1);

  const symbol_exprt qvar = fresh_symbol("QA_equal_ignore_case", index_type);
  const exprt constr2 =
    character_equals_ignore_case(s1[qvar], s2[qvar], char_a, char_A, char_Z);
  const string_constraintt a2(
    qvar, zero_if_negative(s1.length()), implies_exprt(eq, constr2));
  constraints.universal.push_back(a2);

  const symbol_exprt witness =
    fresh_symbol("witness_unequal_ignore_case", index_type);
  const exprt zero = from_integer(0, witness.type());
  const and_exprt bound_witness(
    binary_relation_exprt(witness, ID_lt, s1.length()),
    binary_relation_exprt(witness, ID_ge, zero));
  const exprt witness_eq = character_equals_ignore_case(
    s1[witness], s2[witness], char_a, char_A, char_Z);
  const not_exprt witness_diff(witness_eq);
  const implies_exprt a3(
    not_exprt(eq),
    or_exprt(
      notequal_exprt(s1.length(), s2.length()),
      and_exprt(bound_witness, witness_diff)));
  constraints.existential.push_back(a3);

  return {typecast_exprt(eq, f.type()), std::move(constraints)};
}

/// Value that is identical for strings with the same content
///
/// Add axioms stating that if two strings are equal then the values
/// returned by this function are equal.
/// These axioms are, for each string `s` on which hash was called:
///   * \f$ hash(str)=hash(s) \lor |str| \ne |s|
///       \lor (|str|=|s| \land \exists i<|s|.\ s[i]\ne str[i]) \f$
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with argument refined_string `str`
/// \param pool: pool of arrays representing strings
/// \return integer expression `hash(str)`
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_hash_code(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &pool)
{
  PRECONDITION(f.arguments().size() == 1);
  string_constraintst constraints;
  const array_string_exprt str = get_string_expr(pool, f.arguments()[0]);
  const typet &return_type = f.type();
  const typet &index_type = str.length().type();

  auto pair=hash_code_of_string.insert(
    std::make_pair(str, fresh_symbol("hash", return_type)));
  const exprt hash = pair.first->second;

  for(auto it : hash_code_of_string)
  {
    const symbol_exprt i = fresh_symbol("index_hash", index_type);
    const equal_exprt c1(it.second, hash);
    const notequal_exprt c2(it.first.length(), str.length());
    const and_exprt c3(
      equal_exprt(it.first.length(), str.length()),
      and_exprt(
        notequal_exprt(str[i], it.first[i]),
        and_exprt(axiom_for_length_gt(str, i), is_positive(i))));
    constraints.existential.push_back(or_exprt(c1, or_exprt(c2, c3)));
  }
  return {hash, std::move(constraints)};
}

/// Lexicographic comparison of two strings
///
/// Add axioms ensuring the result corresponds to that of the `String.compareTo`
/// Java function.
/// In the lexicographic comparison, `x` representing the first point where the
/// two strings differ, we add axioms:
///   * \f$ res=0 \Rightarrow |s1|=|s2|\f$
///   * \f$ \forall i<|s1|. s1[i]=s2[i] \f$
///   * \f$ \exists x.\ res\ne 0 \Rightarrow x > 0
///         \land ((|s1| \ge |s2| \land x<|s1|)
///                \lor (|s1| \ge |s2| \land x<|s2|)
///         \land res=s1[x]-s2[x] )
///         \lor cond2:
///         (|s1|<|s2| \land x=|s1|) \lor (|s1| > |s2| \land x=|s2|)
///         \land res=|s1|-|s2|) \f$
///   * \f$ \forall i'<x. res\ne 0 \Rightarrow s1[i]=s2[i] \f$
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with arguments refined_string `s1`
///           and refined_string `s2`
/// \param pool: pool of arrays representing strings
/// \return integer expression `res`
std::pair<exprt, string_constraintst> add_axioms_for_compare_to(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &pool)
{
  PRECONDITION(f.arguments().size() == 2);
  const typet &return_type=f.type();
  PRECONDITION(return_type.id() == ID_signedbv);
  string_constraintst constraints;
  const array_string_exprt &s1 = get_string_expr(pool, f.arguments()[0]);
  const array_string_exprt &s2 = get_string_expr(pool, f.arguments()[1]);
  const symbol_exprt res = fresh_symbol("compare_to", return_type);
  const typet &index_type = s1.length().type();

  const equal_exprt res_null(res, from_integer(0, return_type));
  const implies_exprt a1(res_null, equal_exprt(s1.length(), s2.length()));
  constraints.existential.push_back(a1);

  const symbol_exprt i = fresh_symbol("QA_compare_to", index_type);
  const string_constraintt a2(
    i,
    zero_if_negative(s1.length()),
    implies_exprt(res_null, equal_exprt(s1[i], s2[i])));
  constraints.universal.push_back(a2);

  const symbol_exprt x = fresh_symbol("index_compare_to", index_type);
  const equal_exprt ret_char_diff(
    res,
    minus_exprt(
      typecast_exprt(s1[x], return_type), typecast_exprt(s2[x], return_type)));
  const equal_exprt ret_length_diff(
    res,
    minus_exprt(
      typecast_exprt(s1.length(), return_type),
      typecast_exprt(s2.length(), return_type)));
  const or_exprt guard1(
    and_exprt(axiom_for_length_le(s1, s2.length()), axiom_for_length_gt(s1, x)),
    and_exprt(length_ge(s1, s2.length()), axiom_for_length_gt(s2, x)));
  const and_exprt cond1(ret_char_diff, guard1);
  const or_exprt guard2(
    and_exprt(
      axiom_for_length_gt(s2, s1.length()), axiom_for_has_length(s1, x)),
    and_exprt(
      axiom_for_length_gt(s1, s2.length()), axiom_for_has_length(s2, x)));
  const and_exprt cond2(ret_length_diff, guard2);

  const implies_exprt a3(
    not_exprt(res_null),
    and_exprt(
      binary_relation_exprt(x, ID_ge, from_integer(0, return_type)),
      or_exprt(cond1, cond2)));
  constraints.existential.push_back(a3);

  const symbol_exprt i2 = fresh_symbol("QA_compare_to", index_type);
  const string_constraintt a4(
    i2,
    zero_if_negative(x),
    implies_exprt(not_exprt(res_null), equal_exprt(s1[i2], s2[i2])));
  constraints.universal.push_back(a4);

  return {res, std::move(constraints)};
}

/// Add axioms stating that the return value for two equal string should be the
/// same
/// \deprecated never tested
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with one string argument
/// \return a string expression
DEPRECATED("never tested")
std::pair<symbol_exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_intern(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 1);
  string_constraintst constraints;
  const array_string_exprt str = get_string_expr(array_pool, f.arguments()[0]);
  // For now we only enforce content equality and not pointer equality
  const typet &return_type=f.type();
  const typet index_type = str.length().type();

  auto pair=intern_of_string.insert(
    std::make_pair(str, fresh_symbol("pool", return_type)));
  const symbol_exprt intern = pair.first->second;

  // intern(str)=s_0 || s_1 || ...
  // for each string s.
  //    intern(str)=intern(s) || |str|!=|s|
  //    || (|str|==|s| &&exists i<|s|. s[i]!=str[i])

  exprt::operandst disj;
  for(auto it : intern_of_string)
    disj.push_back(equal_exprt(intern, it.second));
  constraints.existential.push_back(disjunction(disj));

  // WARNING: the specification may be incomplete or incorrect
  for(auto it : intern_of_string)
    if(it.second!=str)
    {
      symbol_exprt i = fresh_symbol("index_intern", index_type);
      constraints.existential.push_back(
        or_exprt(
          equal_exprt(it.second, intern),
          or_exprt(
            notequal_exprt(str.length(), it.first.length()),
            and_exprt(
              equal_exprt(str.length(), it.first.length()),
              and_exprt(
                notequal_exprt(str[i], it.first[i]),
                and_exprt(axiom_for_length_gt(str, i), is_positive(i)))))));
    }

  return {intern, std::move(constraints)};
}
