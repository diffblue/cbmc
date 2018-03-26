/// Module: String solver
/// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_BUILTIN_FUNCTION_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_BUILTIN_FUNCTION_H

#include <vector>
#include <util/optional.h>
#include <util/string_expr.h>
#include "string_constraint_generator.h"

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

  /// Add constraints ensuring that the value of result expression of the
  /// builtin function corresponds to the value of the function call.
  virtual exprt
  add_constraints(string_constraint_generatort &constraint_generator) const = 0;

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
  explicit string_builtin_functiont(const exprt &return_code)
    : return_code(return_code)
  {
  }
};

/// String builtin_function transforming one string into another
class string_transformation_builtin_functiont : public string_builtin_functiont
{
public:
  array_string_exprt result;
  array_string_exprt input;
  std::vector<exprt> args;

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

  /// Evaluate the result from a concrete valuation of the arguments
  virtual std::vector<mp_integer> eval(
    const std::vector<mp_integer> &input_value,
    const std::vector<mp_integer> &args_value) const = 0;

  optionalt<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const override;

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
  }

  std::vector<mp_integer> eval(
    const std::vector<mp_integer> &input_value,
    const std::vector<mp_integer> &args_value) const override;

  std::string name() const override
  {
    return "concat_char";
  }

  exprt add_constraints(string_constraint_generatort &generator) const override
  {
    return generator.add_axioms_for_concat_char(result, input, args[0]);
  }

  exprt length_constraint() const override
  {
    return length_constraint_for_concat_char(result, input);
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

  exprt add_constraints(string_constraint_generatort &generator) const override
  {
    if(args.size() == 1)
      return generator.add_axioms_for_insert(result, input1, input2, args[0]);
    if(args.size() == 3)
      UNIMPLEMENTED;
    UNREACHABLE;
  };

  exprt length_constraint() const override
  {
    if(args.size() == 1)
      return length_constraint_for_insert(result, input1, input2, args[0]);
    if(args.size() == 3)
      UNIMPLEMENTED;
    UNREACHABLE;
  };

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

  exprt add_constraints(string_constraint_generatort &generator) const override
  {
    if(args.size() == 0)
      return generator.add_axioms_for_concat(result, input1, input2);
    if(args.size() == 2)
      return generator.add_axioms_for_concat_substr(
        result, input1, input2, args[0], args[1]);
    UNREACHABLE;
  };

  exprt length_constraint() const override
  {
    if(args.size() == 0)
      return length_constraint_for_concat(result, input1, input2);
    if(args.size() == 2)
      return length_constraint_for_concat_substr(
        result, input1, input2, args[0], args[1]);
    UNREACHABLE;
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

  bool maybe_testing_function() const override
  {
    return false;
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

/// Functions that are not yet supported in this class but are supported by
/// string_constraint_generatort.
/// \note Ultimately this should be disappear, once all builtin function have
///       a corresponding string_builtin_functiont class.
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
  eval(const std::function<exprt(const exprt &)> &get_value) const override
  {
    return {};
  }

  exprt add_constraints(string_constraint_generatort &generator) const override
  {
    return generator.add_axioms_for_function_application(function_application);
  };

  exprt length_constraint() const override
  {
    // For now, there is no need for implementing that as `add_constraints`
    // should always be called on these functions
    UNIMPLEMENTED;
  }
};

#endif // CPROVER_SOLVERS_REFINEMENT_STRING_BUILTIN_FUNCTION_H
