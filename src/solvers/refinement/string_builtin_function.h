/// Module: String solver
/// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_BUILTIN_FUNCTION_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_BUILTIN_FUNCTION_H

#include <vector>
#include <util/optional.h>
#include <util/string_expr.h>
#include "string_constraint_generator.h"

class array_poolt;
struct string_constraintst;
class string_constraint_generatort;

#define CHARACTER_FOR_UNKNOWN '?'

/// Base class for string functions that are built in the solver
class string_builtin_functiont
{
public:
  string_builtin_functiont(const string_builtin_functiont &) = delete;
  virtual ~string_builtin_functiont() = default;

  virtual optionalt<array_string_exprt> string_result() const
  {
    return {};
  }

  virtual std::vector<array_string_exprt> string_arguments() const
  {
    return {};
  }

  /// Given a function `get_value` which gives a valuation to expressions,
  /// attempt to find the result of the builtin function.
  /// If not enough information can be gathered from `get_value`, return an
  /// empty optional.
  virtual optionalt<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const = 0;

  virtual std::string name() const = 0;

  /// Add constraints ensuring that the value of result expression of the
  /// builtin function corresponds to the value of the function call.
  virtual string_constraintst
  constraints(string_constraint_generatort &constraint_generator) const = 0;

  /// Constraint ensuring that the length of the strings are coherent with
  /// the function call.
  virtual exprt length_constraint() const = 0;

  exprt return_code;

  /// Tells whether the builtin function can be a testing function, that is a
  /// function that does not return a string, for instance like `equals`,
  /// `indexOf` or `compare`.
  virtual bool maybe_testing_function() const
  {
    return true;
  }

private:
  string_builtin_functiont() = default;

protected:
  explicit string_builtin_functiont(exprt return_code)
    : return_code(std::move(return_code))
  {
  }
};

/// String builtin_function transforming one string into another
class string_transformation_builtin_functiont : public string_builtin_functiont
{
public:
  array_string_exprt result;
  array_string_exprt input;

  string_transformation_builtin_functiont(
    exprt return_code,
    array_string_exprt result,
    array_string_exprt input)
    : string_builtin_functiont(std::move(return_code)),
      result(std::move(result)),
      input(std::move(input))
  {
  }

  /// Constructor from arguments of a function application.
  /// The arguments in `fun_args` should be in order:
  /// an integer `result.length`, a character pointer `&result[0]`,
  /// a string `arg1` of type refined_string_typet, and potentially some
  /// arguments of primitive types.
  string_transformation_builtin_functiont(
    const exprt &return_code,
    const std::vector<exprt> &fun_args,
    array_poolt &array_pool);

  optionalt<array_string_exprt> string_result() const override
  {
    return result;
  }
  std::vector<array_string_exprt> string_arguments() const override
  {
    return {input};
  }
  bool maybe_testing_function() const override
  {
    return false;
  }
};

/// Adding a character at the end of a string
class string_concat_char_builtin_functiont
  : public string_transformation_builtin_functiont
{
public:
  exprt character;

  /// Constructor from arguments of a function application.
  /// The arguments in `fun_args` should be in order:
  /// an integer `result.length`, a character pointer `&result[0]`,
  /// a string `arg1` of type refined_string_typet, and a character.
  string_concat_char_builtin_functiont(
    const exprt &return_code,
    const std::vector<exprt> &fun_args,
    array_poolt &array_pool)
    : string_transformation_builtin_functiont(return_code, fun_args, array_pool)
  {
    PRECONDITION(fun_args.size() == 4);
    character = fun_args[3];
  }

  optionalt<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const override;

  std::string name() const override
  {
    return "concat_char";
  }

  string_constraintst
  constraints(string_constraint_generatort &generator) const override;

  exprt length_constraint() const override;
};

/// Setting a character at a particular position of a string
class string_set_char_builtin_functiont
  : public string_transformation_builtin_functiont
{
public:
  exprt position;
  exprt character;

  /// Constructor from arguments of a function application.
  /// The arguments in `fun_args` should be in order:
  /// an integer `result.length`, a character pointer `&result[0]`,
  /// a string `arg1` of type refined_string_typet, a position and a character.
  string_set_char_builtin_functiont(
    const exprt &return_code,
    const std::vector<exprt> &fun_args,
    array_poolt &array_pool)
    : string_transformation_builtin_functiont(return_code, fun_args, array_pool)
  {
    PRECONDITION(fun_args.size() == 5);
    position = fun_args[3];
    character = fun_args[4];
  }

  optionalt<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const override;

  std::string name() const override
  {
    return "set_char";
  }

  string_constraintst
  constraints(string_constraint_generatort &generator) const override;

  // \todo: length_constraint is not the best possible name because we also
  // \todo: add constraint about the return code
  exprt length_constraint() const override;
};

/// Converting each uppercase character of Basic Latin and Latin-1 supplement
/// to the corresponding lowercase character.
class string_to_lower_case_builtin_functiont
  : public string_transformation_builtin_functiont
{
public:
  string_to_lower_case_builtin_functiont(
    const exprt &return_code,
    const std::vector<exprt> &fun_args,
    array_poolt &array_pool)
    : string_transformation_builtin_functiont(return_code, fun_args, array_pool)
  {
  }

  optionalt<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const override;

  std::string name() const override
  {
    return "to_lower_case";
  }

  string_constraintst
  constraints(string_constraint_generatort &generator) const override;

  exprt length_constraint() const override
  {
    return and_exprt(
      equal_exprt(result.length(), input.length()),
      equal_exprt(return_code, from_integer(0, return_code.type())));
  };
};

/// Converting each lowercase character of Basic Latin and Latin-1 supplement
/// to the corresponding uppercase character.
class string_to_upper_case_builtin_functiont
  : public string_transformation_builtin_functiont
{
public:
  string_to_upper_case_builtin_functiont(
    const exprt &return_code,
    const std::vector<exprt> &fun_args,
    array_poolt &array_pool)
    : string_transformation_builtin_functiont(return_code, fun_args, array_pool)
  {
  }

  string_to_upper_case_builtin_functiont(
    exprt return_code,
    array_string_exprt result,
    array_string_exprt input)
    : string_transformation_builtin_functiont(
        std::move(return_code),
        std::move(result),
        std::move(input))
  {
  }

  optionalt<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const override;

  std::string name() const override
  {
    return "to_upper_case";
  }

  string_constraintst constraints(class symbol_generatort &fresh_symbol) const;

  string_constraintst
  constraints(string_constraint_generatort &generator) const override
  {
    return constraints(generator.fresh_symbol);
  };

  exprt length_constraint() const override
  {
    return and_exprt(
      equal_exprt(result.length(), input.length()),
      equal_exprt(return_code, from_integer(0, return_code.type())));
  };
};

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
  explicit string_insertion_builtin_functiont(const exprt &return_code)
    : string_builtin_functiont(return_code)
  {
  }
};

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

/// String creation from other types
class string_creation_builtin_functiont : public string_builtin_functiont
{
public:
  array_string_exprt result;
  exprt arg;

  string_creation_builtin_functiont(
    const exprt &return_code,
    const std::vector<exprt> &fun_args,
    array_poolt &array_pool);

  optionalt<array_string_exprt> string_result() const override
  {
    return result;
  }

  bool maybe_testing_function() const override
  {
    return false;
  }
};

/// String creation from integer types
class string_of_int_builtin_functiont : public string_creation_builtin_functiont
{
public:
  string_of_int_builtin_functiont(
    const exprt &return_code,
    const std::vector<exprt> &fun_args,
    array_poolt &array_pool)
    : string_creation_builtin_functiont(return_code, fun_args, array_pool)
  {
    PRECONDITION(fun_args.size() <= 4);
    if(fun_args.size() == 4)
      radix = fun_args[3];
    else
      radix = from_integer(10, arg.type());
  };

  optionalt<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const override;

  std::string name() const override
  {
    return "string_of_int";
  }

  string_constraintst
  constraints(string_constraint_generatort &generator) const override;

  exprt length_constraint() const override;

private:
  exprt radix;
};

/// String test
class string_test_builtin_functiont : public string_builtin_functiont
{
public:
  exprt result;
  std::vector<array_string_exprt> under_test;
  std::vector<exprt> args;
  std::vector<array_string_exprt> string_arguments() const override
  {
    return under_test;
  }
};

/// Functions that are not yet supported in this class but are supported by
/// string_constraint_generatort.
/// \note Ultimately this should be disappear, once all builtin function have
///   a corresponding string_builtin_functiont class.
class string_builtin_function_with_no_evalt : public string_builtin_functiont
{
public:
  function_application_exprt function_application;
  optionalt<array_string_exprt> string_res;
  std::vector<array_string_exprt> string_args;
  std::vector<exprt> args;

  string_builtin_function_with_no_evalt(
    const exprt &return_code,
    const function_application_exprt &f,
    array_poolt &array_pool);

  std::string name() const override
  {
    return id2string(function_application.function().get_identifier());
  }
  std::vector<array_string_exprt> string_arguments() const override
  {
    return std::vector<array_string_exprt>(string_args);
  }
  optionalt<array_string_exprt> string_result() const override
  {
    return string_res;
  }

  optionalt<exprt>
  eval(const std::function<exprt(const exprt &)> &) const override
  {
    return {};
  }

  string_constraintst
  constraints(string_constraint_generatort &generator) const override;

  exprt length_constraint() const override
  {
    // For now, there is no need for implementing that as `constraints`
    // should always be called on these functions
    UNIMPLEMENTED;
  }
};

#endif // CPROVER_SOLVERS_REFINEMENT_STRING_BUILTIN_FUNCTION_H
