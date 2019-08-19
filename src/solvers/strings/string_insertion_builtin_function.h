/*******************************************************************\

Module: String solver

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_STRINGS_STRING_INSERTION_BUILTIN_FUNCTION_H
#define CPROVER_SOLVERS_STRINGS_STRING_INSERTION_BUILTIN_FUNCTION_H

#include "string_builtin_function.h"

/// String inserting a string into another one
class string_insertion_builtin_functiont : public string_builtin_functiont
{
public:
  array_string_exprt result;
  array_string_exprt input1;
  array_string_exprt input2;
  std::vector<exprt> args;

  /// Constructor from arguments of a function application.
  /// The arguments in `fun_args` should be in order:
  /// an integer `result.length`, a character pointer `&result[0]`,
  /// a string `arg1` of type refined_string_typet,
  /// a string `arg2` of type refined_string_typet,
  /// and potentially some arguments of primitive types.
  string_insertion_builtin_functiont(
    const exprt &return_code,
    const std::vector<exprt> &fun_args,
    array_poolt &array_pool);

  optionalt<array_string_exprt> string_result() const override
  {
    return result;
  }
  std::vector<array_string_exprt> string_arguments() const override
  {
    return {input1, input2};
  }

  /// Evaluate the result from a concrete valuation of the arguments
  virtual std::vector<mp_integer> eval(
    const std::vector<mp_integer> &input1_value,
    const std::vector<mp_integer> &input2_value,
    const std::vector<mp_integer> &args_value) const;

  optionalt<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const override;

  std::string name() const override
  {
    return "insert";
  }

  string_constraintst
  constraints(string_constraint_generatort &generator) const override;

  exprt length_constraint() const override;

  bool maybe_testing_function() const override
  {
    return false;
  }

protected:
  string_insertion_builtin_functiont(
    const exprt &return_code,
    array_poolt &array_pool)
    : string_builtin_functiont(return_code, array_pool)
  {
  }
};

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
/// \param array_pool: pool of arrays representing strings
/// \return an expression expression which is different from zero if there is
///   an exception to signal
std::pair<exprt, string_constraintst> add_axioms_for_insert(
  symbol_generatort &fresh_symbol,
  const function_application_exprt &f,
  array_poolt &array_pool);

/// Add axioms ensuring the length of `res` corresponds to that of `s1` where we
/// inserted `s2`.
exprt length_constraint_for_insert(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2,
  array_poolt &array_pool);

#endif // CPROVER_SOLVERS_STRINGS_STRING_INSERTION_BUILTIN_FUNCTION_H
