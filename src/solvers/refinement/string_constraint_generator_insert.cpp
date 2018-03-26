/*******************************************************************\

Module: Generates string constraints for the family of insert Java functions

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for the family of insert Java functions

#include <solvers/refinement/string_refinement_invariant.h>
#include <solvers/refinement/string_constraint_generator.h>

/// Add axioms ensuring the result `res` corresponds to `s1` where we
/// inserted `s2` at position `offset`.
/// We write offset' for `max(0, min(res.length, offset))`.
/// These axioms are:
/// 1. res.length = s1.length + s2.length
/// 2. forall i < offset' . res[i] = s1[i]
/// 3. forall i < s2.length. res[i + offset'] = s2[i]
/// 4. forall i in [offset', s1.length). res[i + s2.length] = s1[i]
/// This is equivalent to
/// `res=concat(substring(s1, 0, offset'), concat(s2, substring(s1, offset')))`.
/// \param res: array of characters expression
/// \param s1: array of characters expression
/// \param s2: array of characters expression
/// \param offset: integer expression
/// \return an expression expression which is different from zero if there is
///         an exception to signal
exprt string_constraint_generatort::add_axioms_for_insert(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2,
  const exprt &offset)
{
  PRECONDITION(offset.type()==s1.length().type());
  const typet &index_type = s1.length().type();
  const exprt offset1 =
    maximum(from_integer(0, index_type), minimum(s1.length(), offset));

  // Axiom 1.
  lemmas.push_back(length_constraint_for_insert(res, s1, s2, offset));

  // Axiom 2.
  constraints.push_back([&] { // NOLINT
    const symbol_exprt i = fresh_symbol("QA_insert1", index_type);
    return string_constraintt(i, offset1, equal_exprt(res[i], s1[i]));
  }());

  // Axiom 3.
  constraints.push_back([&] { // NOLINT
    const symbol_exprt i = fresh_symbol("QA_insert2", index_type);
    return string_constraintt(
      i, s2.length(), equal_exprt(res[plus_exprt(i, offset1)], s2[i]));
  }());

  // Axiom 4.
  constraints.push_back([&] { // NOLINT
    const symbol_exprt i = fresh_symbol("QA_insert3", index_type);
    return string_constraintt(
      i,
      offset1,
      s1.length(),
      equal_exprt(res[plus_exprt(i, s2.length())], s1[i]));
  }());

  return from_integer(0, get_return_code_type());
}

/// Add axioms ensuring the length of `res` corresponds that of `s1` where we
/// inserted `s2` at position `offset`.
exprt length_constraint_for_insert(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2,
  const exprt &offset)
{
  return equal_exprt(res.length(), plus_exprt(s1.length(), s2.length()));
}

/// Insertion of a string in another at a specific index
///
/// \copybrief string_constraint_generatort::add_axioms_for_insert(
/// const array_string_exprt &, const array_string_exprt &,
/// const array_string_exprt &, const exprt &)
// NOLINTNEXTLINE
/// \link add_axioms_for_insert(const array_string_exprt&,const array_string_exprt&,const array_string_exprt&,const exprt&)
///   (More...) \endlink
///
/// If `start` and `end` arguments are given then `substring(s2, start, end)`
/// is considered instead of `s2`.
/// \param f: function application with arguments integer `|res|`, character
///           pointer `&res[0]`, refined_string `s1`, refined_string`s2`,
///           integer `offset`, optional integer `start` and optional integer
///           `end`
/// \return an integer expression which is different from zero if there is
///         an exception to signal
exprt string_constraint_generatort::add_axioms_for_insert(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 5 || f.arguments().size() == 7);
  array_string_exprt s1 = get_string_expr(f.arguments()[2]);
  array_string_exprt s2 = get_string_expr(f.arguments()[4]);
  array_string_exprt res =
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const exprt &offset = f.arguments()[3];
  if(f.arguments().size() == 7)
  {
    const exprt &start = f.arguments()[5];
    const exprt &end = f.arguments()[6];
    const typet &char_type = s1.content().type().subtype();
    const typet &index_type = s1.length().type();
    array_string_exprt substring = fresh_string(index_type, char_type);
    exprt return_code1 = add_axioms_for_substring(substring, s2, start, end);
    exprt return_code2 = add_axioms_for_insert(res, s1, substring, offset);
    return if_exprt(
      equal_exprt(return_code1, from_integer(0, return_code1.type())),
      return_code2,
      return_code1);
  }
  else // 5 arguments
  {
    return add_axioms_for_insert(res, s1, s2, offset);
  }
}

/// add axioms corresponding to the StringBuilder.insert(I) java function
/// \deprecated
/// \param f: function application with three arguments: a string, an
///   integer offset, and an integer
/// \return an expression
exprt string_constraint_generatort::add_axioms_for_insert_int(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 5);
  const array_string_exprt s1 = get_string_expr(f.arguments()[2]);
  const array_string_exprt res =
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const exprt &offset = f.arguments()[3];
  const typet &index_type = s1.length().type();
  const typet &char_type = s1.content().type().subtype();
  array_string_exprt s2 = fresh_string(index_type, char_type);
  exprt return_code = add_axioms_from_int(s2, f.arguments()[4]);
  return add_axioms_for_insert(res, s1, s2, offset);
}

/// add axioms corresponding to the StringBuilder.insert(Z) java function
/// \deprecated should convert the value to string and call insert
/// \param f: function application with three arguments: a string, an
///   integer offset, and a Boolean
/// \return a new string expression
exprt string_constraint_generatort::add_axioms_for_insert_bool(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 5);
  const array_string_exprt s1 = get_string_expr(f.arguments()[0]);
  const array_string_exprt res =
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const exprt &offset = f.arguments()[3];
  const typet &index_type = s1.length().type();
  const typet &char_type = s1.content().type().subtype();
  array_string_exprt s2 = fresh_string(index_type, char_type);
  exprt return_code = add_axioms_from_bool(s2, f.arguments()[4]);
  return add_axioms_for_insert(res, s1, s2, offset);
}

/// Add axioms corresponding to the StringBuilder.insert(C) java function
/// \todo This should be merged with add_axioms_for_insert.
/// \param f: function application with three arguments: a string, an
///   integer offset, and a character
/// \return an expression
exprt string_constraint_generatort::add_axioms_for_insert_char(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 5);
  const array_string_exprt res =
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const array_string_exprt s1 = get_string_expr(f.arguments()[2]);
  const exprt &offset = f.arguments()[3];
  const typet &index_type = s1.length().type();
  const typet &char_type = s1.content().type().subtype();
  array_string_exprt s2 = fresh_string(index_type, char_type);
  exprt return_code = add_axioms_from_char(s2, f.arguments()[4]);
  return add_axioms_for_insert(res, s1, s2, offset);
}

/// add axioms corresponding to the StringBuilder.insert(D) java function
/// \deprecated should convert the value to string and call insert
/// \param f: function application with three arguments: a string, an
///   integer offset, and a double
/// \return a string expression
exprt string_constraint_generatort::add_axioms_for_insert_double(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 5);
  const array_string_exprt res =
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const array_string_exprt s1 = get_string_expr(f.arguments()[2]);
  const exprt &offset = f.arguments()[3];
  const typet &index_type = s1.length().type();
  const typet &char_type = s1.content().type().subtype();
  const array_string_exprt s2 = fresh_string(index_type, char_type);
  const exprt return_code =
    add_axioms_for_string_of_float(s2, f.arguments()[4]);
  return add_axioms_for_insert(res, s1, s2, offset);
}

/// Add axioms corresponding to the StringBuilder.insert(F) java function
/// \deprecated should convert the value to string and call insert
/// \param f: function application with three arguments: a string, an
///   integer offset, and a float
/// \return a new string expression
exprt string_constraint_generatort::add_axioms_for_insert_float(
  const function_application_exprt &f)
{
  return add_axioms_for_insert_double(f);
}
