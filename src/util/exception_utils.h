/*******************************************************************\

Module: Exception helper utilities

Author: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_EXCEPTION_UTILS_H
#define CPROVER_UTIL_EXCEPTION_UTILS_H

#include <string>

#include "source_location.h"

/// Base class for exceptions thrown in the cprover project.
/// Intended to be used as a convenient way to have a
/// "catch all and report errors" from application entry points.
class cprover_exception_baset
{
public:
  /// A human readable description of what went wrong.
  /// For readability, implementors should not add a leading
  /// or trailing newline to this description.
  virtual std::string what() const = 0;
};

/// Thrown when users pass incorrect command line arguments,
/// for example passing no files to analysis or setting
/// two mutually exclusive flags
class invalid_command_line_argument_exceptiont : public cprover_exception_baset
{
  /// The reason this exception was generated.
  std::string reason;
  /// The full command line option (not the argument) that got
  /// erroneous input.
  std::string option;
  /// In case we have samples of correct input to the option.
  std::string correct_input;

public:
  invalid_command_line_argument_exceptiont(
    std::string reason,
    std::string option,
    std::string correct_input = "");

  std::string what() const override;
};

/// Thrown when some external system fails unexpectedly.
/// Examples are IO exceptions (files not present, or we don't
/// have the right permissions to interact with them), timeouts for
/// external processes etc
class system_exceptiont : public cprover_exception_baset
{
public:
  explicit system_exceptiont(std::string message);
  std::string what() const override;

private:
  std::string message;
};

/// Thrown when failing to deserialize a value from some
/// low level format, like JSON or raw bytes
class deserialization_exceptiont : public cprover_exception_baset
{
public:
  explicit deserialization_exceptiont(std::string message);

  std::string what() const override;

private:
  std::string message;
};

/// Thrown when a goto program that's being processed is in an invalid format,
/// for example passing the wrong number of arguments to functions.
/// Note that this only applies to goto programs that are user provided,
/// that internal transformations on goto programs don't produce invalid
/// programs should be guarded by invariants instead.
/// \see invariant.h
class incorrect_goto_program_exceptiont : public cprover_exception_baset
{
public:
  incorrect_goto_program_exceptiont(
    std::string message,
    source_locationt source_location);
  explicit incorrect_goto_program_exceptiont(std::string message);
  std::string what() const override;

private:
  std::string message;
  source_locationt source_location;
};

/// Thrown when we encounter an instruction, parameters to an instruction etc.
/// in a goto program that has some theoretically valid semantics,
/// but that we don't presently have any support for.
class unsupported_operation_exceptiont : public cprover_exception_baset
{
public:
  explicit unsupported_operation_exceptiont(std::string message);
  std::string what() const override;

private:
  /// The unsupported operation causing this fault to occur.
  std::string message;
};

/// Thrown when an unexpected error occurs during the analysis (e.g., when the
/// SAT solver returns an error)
class analysis_exceptiont : public cprover_exception_baset
{
public:
  explicit analysis_exceptiont(std::string reason);
  std::string what() const override;

private:
  /// The reason this exception was generated.
  std::string reason;
};

#endif // CPROVER_UTIL_EXCEPTION_UTILS_H
