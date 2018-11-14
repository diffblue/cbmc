/*******************************************************************\

Module: Generates string constraints for constant strings

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for constant strings

#include <solvers/refinement/string_constraint_generator.h>

#include <util/prefix.h>
#include <util/string_constant.h>
#include <util/unicode.h>

/// Add axioms ensuring that the provided string expression and constant are
/// equal.
/// \param res: array of characters for the result
/// \param sval: a string constant
/// \param guard: condition under which the axiom should apply, true by default
/// \return integer expression equal to zero
std::pair<exprt, string_constraintst> add_axioms_for_constant(
  const array_string_exprt &res,
  irep_idt sval,
  const exprt &guard)
{
  string_constraintst constraints;
  const typet &index_type = res.length().type();
  const typet &char_type = res.content().type().subtype();
  std::string c_str=id2string(sval);
  std::wstring str;

/// \todo We should have a special treatment for java strings when the
/// conversion function is available:
#if 0
  if(mode==ID_java)
    str=utf8_to_utf16_little_endian(c_str);
  else
#endif
    str=widen(c_str);

  for(std::size_t i=0; i<str.size(); i++)
  {
    const exprt idx = from_integer(i, index_type);
    const exprt c = from_integer(str[i], char_type);
    const equal_exprt lemma(res[idx], c);
    constraints.existential.push_back(implies_exprt(guard, lemma));
  }

  const exprt s_length = from_integer(str.size(), index_type);

  constraints.existential.push_back(
    implies_exprt(guard, equal_exprt(res.length(), s_length)));
  return {from_integer(0, get_return_code_type()), std::move(constraints)};
}

/// Add axioms to say that the returned string expression is empty
/// \param f: function application with arguments integer `length` and character
///           pointer `ptr`.
/// \return integer expression equal to zero
std::pair<exprt, string_constraintst> add_axioms_for_empty_string(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size() == 2);
  string_constraintst constraints;
  exprt length = f.arguments()[0];
  constraints.existential.push_back(
    equal_exprt(length, from_integer(0, length.type())));
  return {from_integer(0, get_return_code_type()), std::move(constraints)};
}

/// Convert an expression of type string_typet to a string_exprt
/// \param fresh_symbol: generator of fresh symbols
/// \param res: string expression for the result
/// \param arg: expression of type string typet
/// \param guard: condition under which `res` should be equal to arg
/// \return 0 if constraints were added, 1 if expression could not be handled
///         and no constraint was added. Expression we can handle are of the
///         form \f$ e := "<string constant>" | (expr)? e : e \f$
std::pair<exprt, string_constraintst> add_axioms_for_cprover_string(
  symbol_generatort &fresh_symbol,
  const array_string_exprt &res,
  const exprt &arg,
  const exprt &guard)
{
  if(const auto if_expr = expr_try_dynamic_cast<if_exprt>(arg))
  {
    const and_exprt guard_true(guard, if_expr->cond());
    const and_exprt guard_false(guard, not_exprt(if_expr->cond()));
    return combine_results(
      add_axioms_for_cprover_string(
        fresh_symbol, res, if_expr->true_case(), guard_true),
      add_axioms_for_cprover_string(
        fresh_symbol, res, if_expr->false_case(), guard_false));
  }
  else if(const auto constant_expr = expr_try_dynamic_cast<constant_exprt>(arg))
    return add_axioms_for_constant(res, constant_expr->get_value(), guard);
  else
    return {from_integer(1, get_return_code_type()), {}};
}

/// String corresponding to an internal cprover string
///
/// Add axioms ensuring that the returned string expression is equal to the
/// string literal.
/// \todo The name of the function should be changed to reflect what it does.
/// \param fresh_symbol: generator of fresh symbols
/// \param f: function application with an argument which is a string literal
/// that is a constant with a string value.
/// \param array_pool: pool of arrays representing strings
/// \return string expression
std::pair<exprt, string_constraintst> add_axioms_from_literal(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool)
{
  const function_application_exprt::argumentst &args=f.arguments();
  PRECONDITION(args.size() == 3); // Bad args to string literal?
  const array_string_exprt res =
    char_array_of_pointer(array_pool, args[1], args[0]);
  return add_axioms_for_cprover_string(
    fresh_symbol, res, args[2], true_exprt());
}
