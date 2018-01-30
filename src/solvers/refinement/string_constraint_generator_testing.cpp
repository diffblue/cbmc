/*******************************************************************\

Module: Generates string constraints for string functions that return
        Boolean values

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for string functions that return Boolean values

#include <solvers/refinement/string_refinement_invariant.h>
#include <solvers/refinement/string_constraint_generator.h>

/// Add axioms stating that the returned expression is true exactly when the
/// first string is a prefix of the second one, starting at position offset.
///
/// These axioms are:
///   1. \f$ {\tt isprefix} \Rightarrow |str| \ge |{\tt prefix}|+offset \f$
///   2. \f$ \forall 0 \le qvar<|{\tt prefix}|.\ {\tt isprefix}
///          \Rightarrow s0[witness+{\tt offset}]=s2[witness] \f$
///   3. \f$ !{\tt isprefix} \Rightarrow |{\tt str}|<|{\tt prefix}|+{\tt offset}
///          \lor (0 \le witness<|{\tt prefix}|
///        \land {\tt str}[witness+{\tt offset}] \ne {\tt prefix}[witness])\f$
///
/// \param prefix: an array of characters
/// \param str: an array of characters
/// \param offset: an integer
/// \return Boolean expression `isprefix`
exprt string_constraint_generatort::add_axioms_for_is_prefix(
  const array_string_exprt &prefix,
  const array_string_exprt &str,
  const exprt &offset)
{
  symbol_exprt isprefix=fresh_boolean("isprefix");
  const typet &index_type=str.length().type();

  implies_exprt a1(
    isprefix,
    str.axiom_for_length_ge(plus_exprt_with_overflow_check(
      prefix.length(), offset)));
  lemmas.push_back(a1);

  symbol_exprt qvar=fresh_univ_index("QA_isprefix", index_type);
  string_constraintt a2(
    qvar,
    prefix.length(),
    isprefix,
    equal_exprt(str[plus_exprt(qvar, offset)], prefix[qvar]));
  constraints.push_back(a2);

  symbol_exprt witness=fresh_exist_index("witness_not_isprefix", index_type);
  and_exprt witness_diff(
    axiom_for_is_positive_index(witness),
    and_exprt(
      prefix.axiom_for_length_gt(witness),
      notequal_exprt(str[plus_exprt(witness, offset)], prefix[witness])));
  or_exprt s0_notpref_s1(
    not_exprt(str.axiom_for_length_ge(plus_exprt(prefix.length(), offset))),
    witness_diff);

  implies_exprt a3(not_exprt(isprefix), s0_notpref_s1);
  lemmas.push_back(a3);
  return isprefix;
}

/// Test if the target is a prefix of the string
///
/// Add axioms ensuring the return value is true when the string starts with the
/// given target.
/// These axioms are detailed here:
// NOLINTNEXTLINE
/// string_constraint_generatort::add_axioms_for_is_prefix(const array_string_exprt &prefix, const array_string_exprt &str, const exprt &offset)
/// \todo The primitive should be renamed to `starts_with`.
/// \todo Get rid of the boolean flag.
/// \param f: a function application with arguments refined_string `s0`,
///           refined string `s1` and optional integer argument `offset`
///           whose default value is 0
/// \param swap_arguments: a Boolean telling whether the prefix is the second
///        argument or the first argument
/// \return boolean expression `isprefix`
exprt string_constraint_generatort::add_axioms_for_is_prefix(
  const function_application_exprt &f, bool swap_arguments)
{
  const function_application_exprt::argumentst &args=f.arguments();
  PRECONDITION(f.type()==bool_typet() || f.type().id()==ID_c_bool);
  PRECONDITION(args.size() == 2 || args.size() == 3);
  const array_string_exprt s0 = get_string_expr(args[swap_arguments ? 1 : 0]);
  const array_string_exprt s1 = get_string_expr(args[swap_arguments ? 0 : 1]);
  const exprt offset =
    args.size() == 2 ? from_integer(0, s0.length().type()) : args[2];
  return typecast_exprt(add_axioms_for_is_prefix(s0, s1, offset), f.type());
}

/// Add axioms stating that the returned value is true exactly when the argument
/// string is empty.
/// \deprecated should use `string_length(s)==0` instead
/// \param f: function application with a string argument
/// \return a Boolean expression
exprt string_constraint_generatort::add_axioms_for_is_empty(
  const function_application_exprt &f)
{
  PRECONDITION(f.type()==bool_typet() || f.type().id()==ID_c_bool);
  PRECONDITION(f.arguments().size() == 1);
  // We add axioms:
  // a1 : is_empty => |s0| = 0
  // a2 : s0 => is_empty

  symbol_exprt is_empty=fresh_boolean("is_empty");
  array_string_exprt s0 = get_string_expr(f.arguments()[0]);
  lemmas.push_back(implies_exprt(is_empty, s0.axiom_for_has_length(0)));
  lemmas.push_back(implies_exprt(s0.axiom_for_has_length(0), is_empty));
  return typecast_exprt(is_empty, f.type());
}

/// Test if the target is a suffix of the string
///
/// Add axioms ensuring the return value is true when the first string ends with
/// the given target.
/// These axioms are:
///   1. \f$ \texttt{issuffix} \Rightarrow |s_0| \ge |s_1| \f$
///   2. \f$ \forall i <|s_1|.\ {\tt issuffix}
///          \Rightarrow s_1[i] = s_0[i + |s_0| - |s_1|]
///      \f$
///   3. \f$ \lnot {\tt issuffix} \Rightarrow
///     (|s_1| > |s_0| \land {\tt witness}=-1)
///     \lor (|s_1| > {witness} \ge 0
///       \land s_1[{witness}] \ne s_0[{witness} + |s_0| - |s_1|] \f$
///
/// \todo The primitive should be renamed `ends_with`.
/// \param f: a function application with arguments refined_string `s0`
///           and refined_string  `s1`
/// \param swap_arguments: boolean flag telling whether the suffix is the second
///        argument or the first argument
/// \return Boolean expression `issuffix`
exprt string_constraint_generatort::add_axioms_for_is_suffix(
  const function_application_exprt &f, bool swap_arguments)
{
  const function_application_exprt::argumentst &args=f.arguments();
  PRECONDITION(args.size()==2); // bad args to string issuffix?
  PRECONDITION(f.type()==bool_typet() || f.type().id()==ID_c_bool);

  symbol_exprt issuffix=fresh_boolean("issuffix");
  typecast_exprt tc_issuffix(issuffix, f.type());
  const array_string_exprt &s0 = get_string_expr(args[swap_arguments ? 1 : 0]);
  const array_string_exprt &s1 = get_string_expr(args[swap_arguments ? 0 : 1]);
  const typet &index_type=s0.length().type();

  implies_exprt a1(issuffix, s1.axiom_for_length_ge(s0.length()));
  lemmas.push_back(a1);

  symbol_exprt qvar=fresh_univ_index("QA_suffix", index_type);
  exprt qvar_shifted=plus_exprt(
    qvar, minus_exprt(s1.length(), s0.length()));
  string_constraintt a2(
    qvar, s0.length(), issuffix, equal_exprt(s0[qvar], s1[qvar_shifted]));
  constraints.push_back(a2);

  symbol_exprt witness=fresh_exist_index("witness_not_suffix", index_type);
  exprt shifted=plus_exprt(
    witness, minus_exprt(s1.length(), s0.length()));
  or_exprt constr3(
    and_exprt(
      s0.axiom_for_length_gt(s1.length()),
      equal_exprt(witness, from_integer(-1, index_type))),
    and_exprt(
      notequal_exprt(s0[witness], s1[shifted]),
      and_exprt(
        s0.axiom_for_length_gt(witness),
        axiom_for_is_positive_index(witness))));
  implies_exprt a3(not_exprt(issuffix), constr3);

  lemmas.push_back(a3);
  return tc_issuffix;
}

/// Test whether a string contains another
///
/// Add axioms ensuring the returned value is true when the first string
/// contains the second.
/// These axioms are:
///   1. \f$ contains \Rightarrow |s_0| \ge |s_1| \f$
///   2. \f$ contains \Rightarrow 0 \le startpos \le |s_0|-|s_1| \f$
///   3. \f$ !contains \Rightarrow startpos = -1 \f$
///   4. \f$ \forall qvar < |s_1|.\ contains
///          \Rightarrow s_1[qvar] = s_0[startpos + qvar] \f$
///   5. \f$ \forall startpos \le |s_0|-|s_1|.
///          \ (!contains \land |s_0| \ge |s_1|)
///          \Rightarrow \exists witness < |s_1|.
///          \ s_1[witness] \ne s_0[startpos+witness] \f$
/// \warning slow for target longer than one character
/// \param f: function application with arguments refined_string `s0`
///           refined_string `s1`
/// \return Boolean expression `contains`
exprt string_constraint_generatort::add_axioms_for_contains(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 2);
  PRECONDITION(f.type()==bool_typet() || f.type().id()==ID_c_bool);
  const array_string_exprt s0 = get_string_expr(f.arguments()[0]);
  const array_string_exprt s1 = get_string_expr(f.arguments()[1]);
  const typet &index_type = s0.length().type();
  const symbol_exprt contains = fresh_boolean("contains");
  const symbol_exprt startpos =
    fresh_exist_index("startpos_contains", index_type);

  const implies_exprt a1(contains, s0.axiom_for_length_ge(s1.length()));
  lemmas.push_back(a1);

  minus_exprt length_diff(s0.length(), s1.length());
  and_exprt bounds(
    axiom_for_is_positive_index(startpos),
    binary_relation_exprt(startpos, ID_le, length_diff));
  implies_exprt a2(contains, bounds);
  lemmas.push_back(a2);

  implies_exprt a3(
    not_exprt(contains),
    equal_exprt(startpos, from_integer(-1, index_type)));
  lemmas.push_back(a3);

  symbol_exprt qvar=fresh_univ_index("QA_contains", index_type);
  exprt qvar_shifted=plus_exprt(qvar, startpos);
  string_constraintt a4(
    qvar, s1.length(), contains, equal_exprt(s1[qvar], s0[qvar_shifted]));
  constraints.push_back(a4);

  string_not_contains_constraintt a5(
    from_integer(0, index_type),
    plus_exprt(from_integer(1, index_type), length_diff),
    and_exprt(not_exprt(contains), s0.axiom_for_length_ge(s1.length())),
    from_integer(0, index_type),
    s1.length(),
    s0,
    s1);
  not_contains_constraints.push_back(a5);

  return typecast_exprt(contains, f.type());
}
