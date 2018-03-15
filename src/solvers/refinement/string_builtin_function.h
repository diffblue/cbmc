/// Module: String solver
/// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_BUILTIN_FUNCTION_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_BUILTIN_FUNCTION_H

#include <vector>
#include <util/optional.h>
#include <util/string_expr.h>

class array_poolt;

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

  virtual optionalt<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const = 0;

  virtual std::string name() const = 0;

protected:
  string_builtin_functiont() = default;
};

/// String builtin_function transforming one string into another
class string_transformation_builtin_functiont : public string_builtin_functiont
{
public:
  array_string_exprt result;
  array_string_exprt input;
  std::vector<exprt> args;
  exprt return_code;

  /// Constructor from arguments of a function application
  string_transformation_builtin_functiont(
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

  /// Evaluate the result from a concrete valuation of the arguments
  virtual std::vector<mp_integer> eval(
    const std::vector<mp_integer> &input_value,
    const std::vector<mp_integer> &args_value) const = 0;

  optionalt<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const override;
};

/// Adding a character at the end of a string
class string_concat_char_builtin_functiont
  : public string_transformation_builtin_functiont
{
public:
  string_concat_char_builtin_functiont(
    const std::vector<exprt> &fun_args,
    array_poolt &array_pool)
    : string_transformation_builtin_functiont(fun_args, array_pool)
  {
  }

  std::vector<mp_integer> eval(
    const std::vector<mp_integer> &input_value,
    const std::vector<mp_integer> &args_value) const override;

  std::string name() const override
  {
    return "concat_char";
  }
};

/// String inserting a string into another one
class string_insertion_builtin_functiont : public string_builtin_functiont
{
public:
  array_string_exprt result;
  array_string_exprt input1;
  array_string_exprt input2;
  std::vector<exprt> args;
  exprt return_code;

  /// Constructor from arguments of a function application
  string_insertion_builtin_functiont(
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

protected:
  string_insertion_builtin_functiont() = default;
};

class string_concatenation_builtin_functiont final
  : public string_insertion_builtin_functiont
{
public:
  string_concatenation_builtin_functiont(
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
};

/// String creation from other types
class string_creation_builtin_functiont : public string_builtin_functiont
{
public:
  array_string_exprt result;
  std::vector<exprt> args;
  exprt return_code;

  optionalt<array_string_exprt> string_result() const override
  {
    return result;
  }
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

#endif // CPROVER_SOLVERS_REFINEMENT_STRING_BUILTIN_FUNCTION_H
