/*******************************************************************\

Module: Built-in function for String.format

Author: Romain Brenguier, Joel Allred

\*******************************************************************/

/// \file
///  Built-in function for String.format

#ifndef CPROVER_SOLVERS_STRINGS_STRING_FORMAT_BUILTIN_FUNCTION_H
#define CPROVER_SOLVERS_STRINGS_STRING_FORMAT_BUILTIN_FUNCTION_H

#include "string_builtin_function.h"

class format_specifiert;

/// Built-in function for String.format().
///
/// The intent is to support all conversions described in:
/// https://docs.oracle.com/javase/8/docs/api/java/util/Formatter.html#syntax
///
/// This table indicates whether each conversion is supported in:
/// 1. string content constraint generation (SCC)
/// 2. string content evaluation (SCE)
/// 3. string length constraint generation (SL)
///
/// For more information on what these mean, refer to
/// \ref string_builtin_functiont.
///
///  c  | SCC | SCE | SL
/// --- | --- | --- | ---
/// \%b |  ✔  |  ?  |  ✔
/// \%B |  ?  |  ?  |  ✔
/// \%h |  ❌  |  ❌  |  ❌
/// \%H |  ❌  |  ❌  |  ❌
/// \%s |  ✔  |  ?  |  ✔
/// \%S |  ?  |  ?  |  ✔
/// \%c |  ?  |  ?  |  ✔
/// \%C |  ?  |  ?  |  ✔
/// \%d |  ✔  |  ?  |  ✔
/// \%o |  ❌  |  ❌  |  ❌
/// \%x |  ✔  |  ✔  |  ❌
/// \%X |  ?  |  ✔  |  ❌
/// \%e |  ?  |  ❌  |  ❌
/// \%E |  ?  |  ❌  |  ❌
/// \%f |  ?  |  ❌  |  ❌
/// \%g |  ❌  |  ❌  |  ❌
/// \%G |  ❌  |  ❌  |  ❌
/// \%a |  ❌  |  ❌  |  ❌
/// \%A |  ❌  |  ❌  |  ❌
/// \%t |  ❌  |  ❌  |  ❌
/// \%T |  ❌  |  ❌  |  ❌
/// \%\% | ✔  |  ?  |  ✔
/// \%n |  ✔  |  ?  |  ✔
///
/// ✓ = full support, ? = untested support , ❌ = no support
///
/// The `index` component of the formatter is supported, but the other
/// components (flag, width, precision, dt) are ignored.
class string_format_builtin_functiont final : public string_builtin_functiont
{
public:
  array_string_exprt result;
  /// Only set when the format string is a constant. In the other case, the
  /// result will be non-deterministic
  optionalt<std::string> format_string;
  std::vector<array_string_exprt> inputs;

  /// Constructor from arguments of a function application.
  /// The arguments in `fun_args` should be in order:
  /// an integer `result.length`, a character pointer `&result[0]`,
  /// a string of type refined_string_typet for the format string,
  /// any number of strings of type refined_string_typet.
  string_format_builtin_functiont(
    const exprt &return_code,
    const std::vector<exprt> &fun_args,
    array_poolt &array_pool);

  optionalt<array_string_exprt> string_result() const override
  {
    return result;
  }

  std::vector<array_string_exprt> string_arguments() const override
  {
    return inputs;
  }

  optionalt<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const override;

  std::string name() const override
  {
    return "format";
  }

  string_constraintst
  constraints(string_constraint_generatort &generator) const override;

  exprt length_constraint() const override;

  /// In principle this function could return true, because the content of the
  /// string sometimes needs to be propagated.
  /// This is the case for methods under test that have a test on the length of
  /// the formatted string, which may depend on the content of the string.
  /// For instance, if the format string contains a boolean formatter, the
  /// length of the resulting string depends on the value of the argument
  /// (`true` or `false`, with respective lengths of 4 and 5), which needs
  /// to be propagated.
  /// Since propagating these constraints is costly and unnecessary in most
  /// cases, we set the function to return false, and rely on the user to
  /// propagate the constants explicitly, as it is done in the
  /// `cproverFormatArgument` method of
  /// lib/cbmc/jbmc/lib/java-models-library/src/main/java/java/lang/String.java
  bool maybe_testing_function() const override
  {
    return false;
  }
};

exprt length_of_decimal_int(
  const exprt &integer,
  const typet &length_type,
  const unsigned long base);

exprt length_for_format_specifier(
  const format_specifiert &fs,
  const array_string_exprt &arg,
  const typet &index_type,
  array_poolt &array_pool);

#endif // CPROVER_SOLVERS_STRINGS_STRING_FORMAT_BUILTIN_FUNCTION_H
