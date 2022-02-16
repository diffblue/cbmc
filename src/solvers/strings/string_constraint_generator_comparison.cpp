/*******************************************************************\

Module: Generates string constraints for function comparing strings,
        such as: equals, equalsIgnoreCase, compareTo, hashCode, intern

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for function comparing strings, such as:
///   equals, equalsIgnoreCase, compareTo, hashCode, intern

#include "string_constraint_generator.h"

#include <util/mathematical_expr.h>

/// Equality of the content of two strings
///
/// Add axioms stating that the result is true exactly when the strings
/// represented by the arguments are equal.
/// These axioms are:
///   1. \f$ eq \Rightarrow |s_1|=|s_2|\f$
///   2. \f$ \forall i<|s_1|.\ eq \Rightarrow s_1[i]=s_2[i] \f$
///   3. \f$ \lnot eq \Rightarrow (|s_1| \ne |s_2| \land witness=-1)
///          \lor (0 \le witness<|s_1| \land s_1[witness] \ne s_2[witness]) \f$
/// \param f: function application with arguments refined_string `s1` and
///   refined_string `s2`
/// \return Boolean expression `eq`
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_equals(
  const function_application_exprt &f)
{
  PRECONDITION(f.type() == bool_typet() || f.type().id() == ID_c_bool);
  PRECONDITION(f.arguments().size() == 2);

  string_constraintst constraints;
  array_string_exprt s1 = get_string_expr(array_pool, f.arguments()[0]);
  array_string_exprt s2 = get_string_expr(array_pool, f.arguments()[1]);
  symbol_exprt eq = fresh_symbol("equal");
  typecast_exprt tc_eq(eq, f.type());

  typet index_type = s1.length_type();

  // Axiom 1.
  constraints.existential.push_back(implies_exprt(
    eq,
    equal_exprt(
      array_pool.get_or_create_length(s1),
      array_pool.get_or_create_length(s2))));

  // Axiom 2.
  constraints.universal.push_back([&] {
    const symbol_exprt qvar = fresh_symbol("QA_equal", index_type);
    return string_constraintt(
      qvar,
      zero_if_negative(array_pool.get_or_create_length(s1)),
      implies_exprt(eq, equal_exprt(s1[qvar], s2[qvar])));
  }());

  // Axiom 3.
  constraints.existential.push_back([&] {
    const symbol_exprt witness = fresh_symbol("witness_unequal", index_type);
    const exprt zero = from_integer(0, index_type);
    const and_exprt bound_witness(
      binary_relation_exprt(
        witness, ID_lt, array_pool.get_or_create_length(s1)),
      binary_relation_exprt(witness, ID_ge, zero));
    const and_exprt witnessing(
      bound_witness, notequal_exprt(s1[witness], s2[witness]));
    const and_exprt diff_length(
      notequal_exprt(
        array_pool.get_or_create_length(s1),
        array_pool.get_or_create_length(s2)),
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
/// \param f: function application with arguments refined_string `s1` and
///   refined_string `s2`
/// \return Boolean expression `eq`
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_equals_ignore_case(
  const function_application_exprt &f)
{
  PRECONDITION(f.type() == bool_typet() || f.type().id() == ID_c_bool);
  PRECONDITION(f.arguments().size() == 2);
  string_constraintst constraints;
  const symbol_exprt eq = fresh_symbol("equal_ignore_case");
  const array_string_exprt s1 = get_string_expr(array_pool, f.arguments()[0]);
  const array_string_exprt s2 = get_string_expr(array_pool, f.arguments()[1]);
  const typet char_type = to_type_with_subtype(s1.content().type()).subtype();
  const exprt char_a = from_integer('a', char_type);
  const exprt char_A = from_integer('A', char_type);
  const exprt char_Z = from_integer('Z', char_type);
  const typet index_type = s1.length_type();

  const implies_exprt a1(
    eq,
    equal_exprt(
      array_pool.get_or_create_length(s1),
      array_pool.get_or_create_length(s2)));
  constraints.existential.push_back(a1);

  const symbol_exprt qvar = fresh_symbol("QA_equal_ignore_case", index_type);
  const exprt constr2 =
    character_equals_ignore_case(s1[qvar], s2[qvar], char_a, char_A, char_Z);
  const string_constraintt a2(
    qvar,
    zero_if_negative(array_pool.get_or_create_length(s1)),
    implies_exprt(eq, constr2));
  constraints.universal.push_back(a2);

  const symbol_exprt witness =
    fresh_symbol("witness_unequal_ignore_case", index_type);
  const exprt zero = from_integer(0, witness.type());
  const and_exprt bound_witness(
    binary_relation_exprt(witness, ID_lt, array_pool.get_or_create_length(s1)),
    binary_relation_exprt(witness, ID_ge, zero));
  const exprt witness_eq = character_equals_ignore_case(
    s1[witness], s2[witness], char_a, char_A, char_Z);
  const not_exprt witness_diff(witness_eq);
  const implies_exprt a3(
    not_exprt(eq),
    or_exprt(
      notequal_exprt(
        array_pool.get_or_create_length(s1),
        array_pool.get_or_create_length(s2)),
      and_exprt(bound_witness, witness_diff)));
  constraints.existential.push_back(a3);

  return {typecast_exprt(eq, f.type()), std::move(constraints)};
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
/// \param f: function application with arguments refined_string `s1` and
///   refined_string `s2`
/// \return integer expression `res`
std::pair<exprt, string_constraintst>
string_constraint_generatort::add_axioms_for_compare_to(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 2);
  const typet &return_type = f.type();
  PRECONDITION(return_type.id() == ID_signedbv);
  string_constraintst constraints;
  const array_string_exprt &s1 = get_string_expr(array_pool, f.arguments()[0]);
  const array_string_exprt &s2 = get_string_expr(array_pool, f.arguments()[1]);
  const symbol_exprt res = fresh_symbol("compare_to", return_type);
  const typet &index_type = s1.length_type();

  const equal_exprt res_null(res, from_integer(0, return_type));
  const implies_exprt a1(
    res_null,
    equal_exprt(
      array_pool.get_or_create_length(s1),
      array_pool.get_or_create_length(s2)));
  constraints.existential.push_back(a1);

  const symbol_exprt i = fresh_symbol("QA_compare_to", index_type);
  const string_constraintt a2(
    i,
    zero_if_negative(array_pool.get_or_create_length(s1)),
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
      typecast_exprt(array_pool.get_or_create_length(s1), return_type),
      typecast_exprt(array_pool.get_or_create_length(s2), return_type)));
  const or_exprt guard1(
    and_exprt(
      less_than_or_equal_to(
        array_pool.get_or_create_length(s1),
        array_pool.get_or_create_length(s2)),
      greater_than(array_pool.get_or_create_length(s1), x)),
    and_exprt(
      greater_or_equal_to(
        array_pool.get_or_create_length(s1),
        array_pool.get_or_create_length(s2)),
      greater_than(array_pool.get_or_create_length(s2), x)));
  const and_exprt cond1(ret_char_diff, guard1);
  const or_exprt guard2(
    and_exprt(
      greater_than(
        array_pool.get_or_create_length(s2),
        array_pool.get_or_create_length(s1)),
      equal_to(array_pool.get_or_create_length(s1), x)),
    and_exprt(
      greater_than(
        array_pool.get_or_create_length(s1),
        array_pool.get_or_create_length(s2)),
      equal_to(array_pool.get_or_create_length(s2), x)));
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
