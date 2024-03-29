/// Module: String solver
/// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_BUILTIN_FUNCTION_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_BUILTIN_FUNCTION_H

#include "string_constraint_generator.h"

#include <util/mathematical_expr.h>
#include <util/string_expr.h>

#include <vector>

#define CHARACTER_FOR_UNKNOWN '?'

/// Base class for string functions that are built in the solver.
///
/// The \ref string_dependenciest framework handles string operations by either:
/// 1. generating constraints for the solver, which is done by the
///    `constraints()` function,
/// 2. evaluating constant operations from the solver model, which is done by
///    the `eval()` function.
///
/// Only the content of the strings are managed in that way. The constraints
/// for the lengths are always added, see \ref length_constraint().
///
/// Concretely, if a built-in function supports **constraint generation**, it
/// means that the result of the operation can be tested. For instance in this
/// Java example:
/// ```java
/// String s = "foo" + "bar";
/// if (s.equals("foobar") {
///   assert false;
/// } else {
///   asset false;
/// }
/// ```
/// if the built-in function for concatenation supports constraint generation,
/// then the first assertion is reachable, but the second is not.
///
/// If a built-in function supports **evaluation**, then adding the constraints
/// can be avoided if the string operation is not relevant to the control flow,
/// e.g. in:
/// ```java
/// String s = "foo" + "bar";
/// return s;
/// ```
/// In this case, if concatenation supports evaluation, then the constraints for
/// the concatenation operations are not added, but the concatenation is
/// evaluated after solving, from the model, to render the concatenated string
/// which is needed for generating the trace.
///
/// If the built-in function supports **constraint generation for the string
/// length**, it means that the length of the string can be tested, as in:
/// ```java
/// String s = "foo" + "bar";
/// if (s.length() == 6) {
///   assert false;
/// }
/// ```
/// As computing lengths is often much simpler than computing string
/// constraints, there is no option to only evaluate string lengths from the
/// solver model. String length constraints are generated by
/// \ref length_constraint().
///
/// The decision about whether to add constraints or not is implemented in
/// in \ref string_dependenciest.
///
/// Specific string operations are implemented by inheriting from
/// \ref string_builtin_functiont and implementing the virtual methods.
class string_builtin_functiont
{
public:
  string_builtin_functiont() = delete;
  string_builtin_functiont(const string_builtin_functiont &) = delete;
  virtual ~string_builtin_functiont() = default;

  virtual std::optional<array_string_exprt> string_result() const
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
  virtual std::optional<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const = 0;

  virtual std::string name() const = 0;

  /// Add constraints ensuring that the value of result expression of the
  /// builtin function corresponds to the value of the function call.
  /// The constraints are only added when deemed necessary, i.e. when
  /// maybe_testing_function() returns true, or when testing function depends on
  /// the result of this function.
  /// This logic is implemented in add_constraints().
  virtual string_constraintst
  constraints(string_constraint_generatort &, message_handlert &) const = 0;

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

protected:
  array_poolt &array_pool;

  string_builtin_functiont(exprt return_code, array_poolt &array_pool)
    : return_code(std::move(return_code)), array_pool(array_pool)
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
    array_string_exprt input,
    array_poolt &array_pool)
    : string_builtin_functiont(std::move(return_code), array_pool),
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

  std::optional<array_string_exprt> string_result() const override
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

  std::optional<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const override;

  std::string name() const override
  {
    return "concat_char";
  }

  string_constraintst constraints(
    string_constraint_generatort &generator,
    message_handlert &message_handlert) const override;

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

  std::optional<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const override;

  std::string name() const override
  {
    return "set_char";
  }

  string_constraintst constraints(
    string_constraint_generatort &generator,
    message_handlert &message_handler) const override;

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

  std::optional<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const override;

  std::string name() const override
  {
    return "to_lower_case";
  }

  string_constraintst constraints(
    string_constraint_generatort &generator,
    message_handlert &message_handler) const override;

  exprt length_constraint() const override
  {
    return and_exprt(
      equal_exprt(
        array_pool.get_or_create_length(result),
        array_pool.get_or_create_length(input)),
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
    array_string_exprt input,
    array_poolt &array_pool)
    : string_transformation_builtin_functiont(
        std::move(return_code),
        std::move(result),
        std::move(input),
        array_pool)
  {
  }

  std::optional<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const override;

  std::string name() const override
  {
    return "to_upper_case";
  }

  string_constraintst constraints(
    class symbol_generatort &fresh_symbol,
    message_handlert &message_handler) const;

  string_constraintst constraints(
    string_constraint_generatort &generator,
    message_handlert &message_handler) const override
  {
    return constraints(generator.fresh_symbol, message_handler);
  };

  exprt length_constraint() const override
  {
    return and_exprt(
      equal_exprt(
        array_pool.get_or_create_length(result),
        array_pool.get_or_create_length(input)),
      equal_exprt(return_code, from_integer(0, return_code.type())));
  };
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

  std::optional<array_string_exprt> string_result() const override
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

  std::optional<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const override;

  std::string name() const override
  {
    return "string_of_int";
  }

  string_constraintst constraints(
    string_constraint_generatort &generator,
    message_handlert &message_handler) const override;

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
  std::optional<array_string_exprt> string_res;
  std::vector<array_string_exprt> string_args;
  std::vector<exprt> args;

  string_builtin_function_with_no_evalt(
    const exprt &return_code,
    const function_application_exprt &f,
    array_poolt &array_pool);

  std::string name() const override
  {
    PRECONDITION(function_application.function().id() == ID_symbol);
    return id2string(
      to_symbol_expr(function_application.function()).get_identifier());
  }
  std::vector<array_string_exprt> string_arguments() const override
  {
    return std::vector<array_string_exprt>(string_args);
  }
  std::optional<array_string_exprt> string_result() const override
  {
    return string_res;
  }

  std::optional<exprt>
  eval(const std::function<exprt(const exprt &)> &) const override
  {
    return {};
  }

  string_constraintst constraints(
    string_constraint_generatort &generator,
    message_handlert &message_handler) const override;

  exprt length_constraint() const override
  {
    // For now, there is no need for implementing that as `constraints`
    // should always be called on these functions
    UNIMPLEMENTED;
  }
};

/// Given a function `get_value` which gives a valuation to expressions, attempt
/// to find the current value of the array `a`. If the valuation of some
/// characters are missing, then return an empty optional.
std::optional<std::vector<mp_integer>> eval_string(
  const array_string_exprt &a,
  const std::function<exprt(const exprt &)> &get_value);

/// Make a string from a constant array
array_string_exprt make_string(
  const std::vector<mp_integer> &array,
  const array_typet &array_type);

#endif // CPROVER_SOLVERS_REFINEMENT_STRING_BUILTIN_FUNCTION_H
