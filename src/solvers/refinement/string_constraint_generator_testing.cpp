/*******************************************************************\

Module: Generates string constraints for string functions that return
        Boolean values

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for string functions that return Boolean values

#include <solvers/refinement/string_refinement_invariant.h>
#include <solvers/refinement/string_constraint_generator.h>
#include <util/deprecate.h>

/// Add axioms stating that the returned expression is true exactly when the
/// offset is greater or equal to 0 and the first string is a prefix of the
/// second one, starting at position offset.
///
/// These axioms are:
///   1. isprefix => offset_within_bounds
///   2. forall qvar in [0, |prefix|).
///          isprefix => str[qvar + offset] = prefix[qvar]
///   3. !isprefix => !offset_within_bounds
///                   || 0 <= witness < |prefix|
///                      && str[witness+offset] != prefix[witness]
///
/// where offset_within_bounds is:
///     offset >= 0 && offset <= |str| && |str| - offset >= |prefix|
///
/// \param fresh_symbol: generator of fresh symbols
/// \param prefix: an array of characters
/// \param str: an array of characters
/// \param offset: an integer
/// \return Boolean expression `isprefix`
std::pair<exprt, string_constraintst> add_axioms_for_is_prefix(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &prefix,
  const array_string_exprt &str,
  const exprt &offset)
{
  string_constraintst constraints;
  const symbol_exprt isprefix = fresh_symbol("isprefix");
  const typet &index_type = str.length().type();
  const exprt offset_within_bounds = and_exprt(
    binary_relation_exprt(offset, ID_ge, from_integer(0, offset.type())),
    binary_relation_exprt(offset, ID_le, str.length()),
    binary_relation_exprt(
      minus_exprt(str.length(), offset), ID_ge, prefix.length()));

  // Axiom 1.
  constraints.existential.push_back(
    implies_exprt(isprefix, offset_within_bounds));

  // Axiom 2.
  constraints.universal.push_back([&] {
    const symbol_exprt qvar = fresh_symbol("QA_isprefix", index_type);
    const exprt body = implies_exprt(
      isprefix, equal_exprt(str[plus_exprt(qvar, offset)], prefix[qvar]));
    return string_constraintt(
      qvar, maximum(from_integer(0, index_type), prefix.length()), body);
  }());

  // Axiom 3.
  constraints.existential.push_back([&] {
    const exprt witness = fresh_symbol("witness_not_isprefix", index_type);
    const exprt strings_differ_at_witness = and_exprt(
      is_positive(witness),
      axiom_for_length_gt(prefix, witness),
      notequal_exprt(str[plus_exprt(witness, offset)], prefix[witness]));
    const exprt s1_does_not_start_with_s0 = or_exprt(
      not_exprt(offset_within_bounds),
      not_exprt(axiom_for_length_ge(str, plus_exprt(prefix.length(), offset))),
      strings_differ_at_witness);
    return implies_exprt(not_exprt(isprefix), s1_does_not_start_with_s0);
  }());

  return {isprefix, std::move(constraints)};
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
/// \param fresh_symbol: generator of fresh symbols
/// \param f: a function application with arguments refined_string `s0`,
///           refined string `s1` and optional integer argument `offset`
///           whose default value is 0
/// \param swap_arguments: a Boolean telling whether the prefix is the second
///        argument or the first argument
/// \param array_pool: pool of arrays representing strings
/// \return boolean expression `isprefix`
std::pair<exprt, string_constraintst> add_axioms_for_is_prefix(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  bool swap_arguments,
  array_poolt &array_pool)
{
  const function_application_exprt::argumentst &args=f.arguments();
  PRECONDITION(f.type()==bool_typet() || f.type().id()==ID_c_bool);
  PRECONDITION(args.size() == 2 || args.size() == 3);
  const array_string_exprt &s0 =
    get_string_expr(array_pool, args[swap_arguments ? 1u : 0u]);
  const array_string_exprt &s1 =
    get_string_expr(array_pool, args[swap_arguments ? 0u : 1u]);
  const exprt offset =
    args.size() == 2 ? from_integer(0, s0.length().type()) : args[2];
  auto pair = add_axioms_for_is_prefix(fresh_symbol, s0, s1, offset);
  return {typecast_exprt(pair.first, f.type()), std::move(pair.second)};
}

/// Add axioms stating that the returned value is true exactly when the argument
/// string is empty.
/// \deprecated should use `string_length(s)==0` instead
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with a string argument
/// \param array_pool: pool of arrays representing strings
/// \return a Boolean expression
DEPRECATED("should use `string_length(s)==0` instead")
std::pair<exprt, string_constraintst> add_axioms_for_is_empty(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  PRECONDITION(f.type()==bool_typet() || f.type().id()==ID_c_bool);
  PRECONDITION(f.arguments().size() == 1);
  // We add axioms:
  // a1 : is_empty => |s0| = 0
  // a2 : s0 => is_empty

  symbol_exprt is_empty = fresh_symbol("is_empty");
  array_string_exprt s0 = get_string_expr(array_pool, f.arguments()[0]);
  std::vector<exprt> constraints;
  constraints.push_back(implies_exprt(is_empty, axiom_for_has_length(s0, 0)));
  constraints.push_back(implies_exprt(axiom_for_has_length(s0, 0), is_empty));
  return {typecast_exprt(is_empty, f.type()), {constraints}};
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
/// \param fresh_symbol: generator of fresh symbols
/// \param f: a function application with arguments refined_string `s0`
///           and refined_string  `s1`
/// \param swap_arguments: boolean flag telling whether the suffix is the second
///        argument or the first argument
/// \param array_pool: pool of arrays representing strings
/// \return Boolean expression `issuffix`
DEPRECATED("should use `strings_startwith(s0, s1, s1.length - s0.length)`")
std::pair<exprt, string_constraintst> add_axioms_for_is_suffix(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  bool swap_arguments,
  array_poolt &array_pool)
{
  const function_application_exprt::argumentst &args=f.arguments();
  PRECONDITION(args.size()==2); // bad args to string issuffix?
  PRECONDITION(f.type()==bool_typet() || f.type().id()==ID_c_bool);

  string_constraintst constraints;
  symbol_exprt issuffix = fresh_symbol("issuffix");
  typecast_exprt tc_issuffix(issuffix, f.type());
  const array_string_exprt &s0 =
    get_string_expr(array_pool, args[swap_arguments ? 1u : 0u]);
  const array_string_exprt &s1 =
    get_string_expr(array_pool, args[swap_arguments ? 0u : 1u]);
  const typet &index_type=s0.length().type();

  implies_exprt a1(issuffix, axiom_for_length_ge(s1, s0.length()));
  constraints.existential.push_back(a1);

  symbol_exprt qvar = fresh_symbol("QA_suffix", index_type);
  const plus_exprt qvar_shifted(qvar, minus_exprt(s1.length(), s0.length()));
  string_constraintt a2(
    qvar,
    zero_if_negative(s0.length()),
    implies_exprt(issuffix, equal_exprt(s0[qvar], s1[qvar_shifted])));
  constraints.universal.push_back(a2);

  symbol_exprt witness = fresh_symbol("witness_not_suffix", index_type);
  const plus_exprt shifted(witness, minus_exprt(s1.length(), s0.length()));
  or_exprt constr3(
    and_exprt(
      axiom_for_length_gt(s0, s1.length()),
      equal_exprt(witness, from_integer(-1, index_type))),
    and_exprt(
      notequal_exprt(s0[witness], s1[shifted]),
      and_exprt(axiom_for_length_gt(s0, witness), is_positive(witness))));
  implies_exprt a3(not_exprt(issuffix), constr3);

  constraints.existential.push_back(a3);
  return {tc_issuffix, std::move(constraints)};
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
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with arguments refined_string `s0`
///           refined_string `s1`
/// \param array_pool: pool of arrays representing strings
/// \return Boolean expression `contains`
std::pair<exprt, string_constraintst> add_axioms_for_contains(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  PRECONDITION(f.arguments().size() == 2);
  PRECONDITION(f.type()==bool_typet() || f.type().id()==ID_c_bool);
  string_constraintst constraints;
  const array_string_exprt s0 = get_string_expr(array_pool, f.arguments()[0]);
  const array_string_exprt s1 = get_string_expr(array_pool, f.arguments()[1]);
  const typet &index_type = s0.length().type();
  const symbol_exprt contains = fresh_symbol("contains");
  const symbol_exprt startpos = fresh_symbol("startpos_contains", index_type);

  const implies_exprt a1(contains, axiom_for_length_ge(s0, s1.length()));
  constraints.existential.push_back(a1);

  minus_exprt length_diff(s0.length(), s1.length());
  and_exprt bounds(
    is_positive(startpos), binary_relation_exprt(startpos, ID_le, length_diff));
  implies_exprt a2(contains, bounds);
  constraints.existential.push_back(a2);

  implies_exprt a3(
    not_exprt(contains),
    equal_exprt(startpos, from_integer(-1, index_type)));
  constraints.existential.push_back(a3);

  symbol_exprt qvar = fresh_symbol("QA_contains", index_type);
  const plus_exprt qvar_shifted(qvar, startpos);
  string_constraintt a4(
    qvar,
    zero_if_negative(s1.length()),
    implies_exprt(contains, equal_exprt(s1[qvar], s0[qvar_shifted])));
  constraints.universal.push_back(a4);

  const string_not_contains_constraintt a5 = {
    from_integer(0, index_type),
    plus_exprt(from_integer(1, index_type), length_diff),
    and_exprt(not_exprt(contains), axiom_for_length_ge(s0, s1.length())),
    from_integer(0, index_type),
    s1.length(),
    s0,
    s1};
  constraints.not_contains.push_back(a5);

  return {typecast_exprt(contains, f.type()), std::move(constraints)};
}
