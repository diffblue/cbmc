/*******************************************************************\

Module: Builtin functions for string concatenations

Author: Romain Brenguier, Joel Allred

\*******************************************************************/

/// \file
/// Builtin functions for string concatenations

#ifndef CPROVER_SOLVERS_STRINGS_STRING_CONCATENATION_BUILTIN_FUNCTION_H
#define CPROVER_SOLVERS_STRINGS_STRING_CONCATENATION_BUILTIN_FUNCTION_H

#include "string_builtin_function.h"
#include "string_insertion_builtin_function.h"

class string_concatenation_builtin_functiont final
  : public string_insertion_builtin_functiont
{
public:
  /// Constructor from arguments of a function application.
  /// The arguments in `fun_args` should be in order:
  /// an integer `result.length`, a character pointer `&result[0]`,
  /// a string `arg1` of type refined_string_typet,
  /// a string `arg2` of type refined_string_typet,
  /// optionally followed by an integer `start` and an integer `end`.
  string_concatenation_builtin_functiont(
    const exprt &return_code,
    const std::vector<exprt> &fun_args,
    array_poolt &array_pool);

  std::vector<mp_integer> eval(
    const std::vector<mp_integer> &input1_value,
    const std::vector<mp_integer> &input2_value,
    const std::vector<mp_integer> &args_value) const override;

  std::string name() const override
  {
    return "concat";
  }

  string_constraintst
  constraints(string_constraint_generatort &generator) const override;

  exprt length_constraint() const override;
};

#endif // CPROVER_SOLVERS_STRINGS_STRING_CONCATENATION_BUILTIN_FUNCTION_H
