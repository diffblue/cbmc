/*******************************************************************\

Module: Generates string constraints for the family of insert Java functions

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for the family of insert Java functions

#include "string_refinement_invariant.h"
#include "string_constraint_generator.h"

#include <util/deprecate.h>

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
/// \param fresh_symbol: generator of fresh symbols
/// \param res: array of characters expression
/// \param s1: array of characters expression
/// \param s2: array of characters expression
/// \param offset: integer expression
/// \return an expression expression which is different from zero if there is
///   an exception to signal
std::pair<exprt, string_constraintst> add_axioms_for_insert(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2,
  const exprt &offset)
{
  PRECONDITION(offset.type()==s1.length().type());

  string_constraintst constraints;
  const typet &index_type = s1.length().type();
  const exprt offset1 =
    maximum(from_integer(0, index_type), minimum(s1.length(), offset));

  // Axiom 1.
  constraints.existential.push_back(length_constraint_for_insert(res, s1, s2));

  // Axiom 2.
  constraints.universal.push_back([&] { // NOLINT
    const symbol_exprt i = fresh_symbol("QA_insert1", index_type);
    return string_constraintt(i, offset1, equal_exprt(res[i], s1[i]));
  }());

  // Axiom 3.
  constraints.universal.push_back([&] { // NOLINT
    const symbol_exprt i = fresh_symbol("QA_insert2", index_type);
    return string_constraintt(
      i,
      zero_if_negative(s2.length()),
      equal_exprt(res[plus_exprt(i, offset1)], s2[i]));
  }());

  // Axiom 4.
  constraints.universal.push_back([&] { // NOLINT
    const symbol_exprt i = fresh_symbol("QA_insert3", index_type);
    return string_constraintt(
      i,
      offset1,
      zero_if_negative(s1.length()),
      equal_exprt(res[plus_exprt(i, s2.length())], s1[i]));
  }());

  return {from_integer(0, get_return_code_type()), std::move(constraints)};
}

/// Add axioms ensuring the length of `res` corresponds to that of `s1` where we
/// inserted `s2`.
exprt length_constraint_for_insert(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2)
{
  return equal_exprt(res.length(), plus_exprt(s1.length(), s2.length()));
}

/// Insertion of a string in another at a specific index
///
// NOLINTNEXTLINE
/// \copybrief add_axioms_for_insert(symbol_generatort &fresh_symbol, const array_string_exprt &, const array_string_exprt &, const array_string_exprt &, const exprt &)
// NOLINTNEXTLINE
/// \link add_axioms_for_insert(symbol_generatort &fresh_symbol, const array_string_exprt&,const array_string_exprt&,const array_string_exprt&,const exprt&)
///   (More...) \endlink
///
/// If `start` and `end` arguments are given then `substring(s2, start, end)`
/// is considered instead of `s2`.
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with arguments integer `|res|`, character
///   pointer `&res[0]`, refined_string `s1`, refined_string`s2`, integer
///   `offset`, optional integer `start` and optional integer `end`
/// \param pool: pool of arrays representing strings
/// \return an integer expression which is different from zero if there is an
///   exception to signal
std::pair<exprt, string_constraintst> add_axioms_for_insert(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &pool)
{
  PRECONDITION(f.arguments().size() == 5 || f.arguments().size() == 7);
  array_string_exprt s1 = get_string_expr(pool, f.arguments()[2]);
  array_string_exprt s2 = get_string_expr(pool, f.arguments()[4]);
  array_string_exprt res =
    char_array_of_pointer(pool, f.arguments()[1], f.arguments()[0]);
  const exprt &offset = f.arguments()[3];
  if(f.arguments().size() == 7)
  {
    const exprt &start = f.arguments()[5];
    const exprt &end = f.arguments()[6];
    const typet &char_type = s1.content().type().subtype();
    const typet &index_type = s1.length().type();
    const array_string_exprt substring =
      pool.fresh_string(index_type, char_type);
    return combine_results(
      add_axioms_for_substring(fresh_symbol, substring, s2, start, end),
      add_axioms_for_insert(fresh_symbol, res, s1, substring, offset));
  }
  else // 5 arguments
  {
    return add_axioms_for_insert(fresh_symbol, res, s1, s2, offset);
  }
}

/// add axioms corresponding to the StringBuilder.insert(I) java function
/// \deprecated should convert the value to string and call insert
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with three arguments: a string, an
///   integer offset, and an integer
/// \param array_pool: pool of arrays representing strings
/// \param ns: namespace
/// \return an expression
DEPRECATED("should convert the value to string and call insert")
std::pair<exprt, string_constraintst> add_axioms_for_insert_int(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool,
  const namespacet &ns)
{
  PRECONDITION(f.arguments().size() == 5);
  const array_string_exprt s1 = get_string_expr(array_pool, f.arguments()[2]);
  const array_string_exprt res =
    char_array_of_pointer(array_pool, f.arguments()[1], f.arguments()[0]);
  const exprt &offset = f.arguments()[3];
  const typet &index_type = s1.length().type();
  const typet &char_type = s1.content().type().subtype();
  const array_string_exprt s2 = array_pool.fresh_string(index_type, char_type);
  return combine_results(
    add_axioms_for_string_of_int(s2, f.arguments()[4], 0, ns),
    add_axioms_for_insert(fresh_symbol, res, s1, s2, offset));
}

/// add axioms corresponding to the StringBuilder.insert(Z) java function
/// \deprecated should convert the value to string and call insert
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with three arguments: a string, an
///   integer offset, and a Boolean
/// \param array_pool: pool of arrays representing strings
/// \return a new string expression
DEPRECATED("should convert the value to string and call insert")
std::pair<exprt, string_constraintst> add_axioms_for_insert_bool(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  PRECONDITION(f.arguments().size() == 5);
  const array_string_exprt s1 = get_string_expr(array_pool, f.arguments()[0]);
  const array_string_exprt res =
    char_array_of_pointer(array_pool, f.arguments()[1], f.arguments()[0]);
  const exprt &offset = f.arguments()[3];
  const typet &index_type = s1.length().type();
  const typet &char_type = s1.content().type().subtype();
  const array_string_exprt s2 = array_pool.fresh_string(index_type, char_type);
  return combine_results(
    add_axioms_from_bool(s2, f.arguments()[4]),
    add_axioms_for_insert(fresh_symbol, res, s1, s2, offset));
}

/// Add axioms corresponding to the StringBuilder.insert(C) java function
/// \todo This should be merged with add_axioms_for_insert.
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with three arguments: a string, an
///   integer offset, and a character
/// \param array_pool: pool of arrays representing strings
/// \return an expression
std::pair<exprt, string_constraintst> add_axioms_for_insert_char(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  PRECONDITION(f.arguments().size() == 5);
  const array_string_exprt res =
    char_array_of_pointer(array_pool, f.arguments()[1], f.arguments()[0]);
  const array_string_exprt s1 = get_string_expr(array_pool, f.arguments()[2]);
  const exprt &offset = f.arguments()[3];
  const typet &index_type = s1.length().type();
  const typet &char_type = s1.content().type().subtype();
  const array_string_exprt s2 = array_pool.fresh_string(index_type, char_type);
  return combine_results(
    add_axioms_from_char(s2, f.arguments()[4]),
    add_axioms_for_insert(fresh_symbol, res, s1, s2, offset));
}

/// add axioms corresponding to the StringBuilder.insert(D) java function
/// \deprecated should convert the value to string and call insert
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with three arguments: a string, an
///   integer offset, and a double
/// \param array_pool: pool of arrays representing strings
/// \param ns: namespace
/// \return a string expression
DEPRECATED("should convert the value to string and call insert")
std::pair<exprt, string_constraintst> add_axioms_for_insert_double(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool,
  const namespacet &ns)
{
  PRECONDITION(f.arguments().size() == 5);
  const array_string_exprt res =
    char_array_of_pointer(array_pool, f.arguments()[1], f.arguments()[0]);
  const array_string_exprt s1 = get_string_expr(array_pool, f.arguments()[2]);
  const exprt &offset = f.arguments()[3];
  const typet &index_type = s1.length().type();
  const typet &char_type = s1.content().type().subtype();
  const array_string_exprt s2 = array_pool.fresh_string(index_type, char_type);
  return combine_results(
    add_axioms_for_string_of_float(
      fresh_symbol, s2, f.arguments()[4], array_pool, ns),
    add_axioms_for_insert(fresh_symbol, res, s1, s2, offset));
}

/// Add axioms corresponding to the StringBuilder.insert(F) java function
/// \deprecated should convert the value to string and call insert
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with three arguments: a string, an
///   integer offset, and a float
/// \param array_pool: pool of arrays representing strings
/// \param ns: namespace
/// \return a new string expression
DEPRECATED("should convert the value to string and call insert")
std::pair<exprt, string_constraintst> add_axioms_for_insert_float(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool,
  const namespacet &ns)
{
  return add_axioms_for_insert_double(fresh_symbol, f, array_pool, ns);
}
