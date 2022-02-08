/*******************************************************************\

Module: Exception helper utilities

Author: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_EXCEPTION_UTILS_H
#define CPROVER_UTIL_EXCEPTION_UTILS_H

#include <string>

#include "invariant.h"
#include "source_location.h"

/// Base class for exceptions thrown in the cprover project.
/// Intended to be used as a convenient way to have a
/// "catch all and report errors" from application entry points.
/// Note that the reason we use a custom base class as opposed to
/// std::exception or one of its derivates to avoid them being accidentally
/// caught by code expecting standard exceptions to be only thrown by the
/// standard library.
class cprover_exception_baset
{
public:
  /// A human readable description of what went wrong.
  /// For readability, implementors should not add a leading
  /// or trailing newline to this description.
  virtual std::string what() const;
  virtual ~cprover_exception_baset() = default;

protected:
  /// This constructor is marked protected to ensure this class isn't used
  /// directly. Deriving classes should be used to more precisely describe the
  /// problem that occurred.
  explicit cprover_exception_baset(std::string reason)
    : reason(std::move(reason))
  {
  }

  /// The reason this exception was generated. This is the string returned by
  /// `what()` unless that method is overridden
  std::string reason;
};

/// Thrown when users pass incorrect command line arguments,
/// for example passing no files to analysis or setting
/// two mutually exclusive flags
class invalid_command_line_argument_exceptiont : public cprover_exception_baset
{
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
};

/// Thrown when failing to deserialize a value from some
/// low level format, like JSON or raw bytes
class deserialization_exceptiont : public cprover_exception_baset
{
public:
  explicit deserialization_exceptiont(std::string message);
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
  explicit incorrect_goto_program_exceptiont(std::string message);

  template <typename Diagnostic, typename... Diagnostics>
  incorrect_goto_program_exceptiont(
    std::string message,
    Diagnostic &&diagnostic,
    Diagnostics &&... diagnostics);

  template <typename... Diagnostics>
  incorrect_goto_program_exceptiont(
    std::string message,
    source_locationt source_location,
    Diagnostics &&... diagnostics);

  std::string what() const override;

private:
  source_locationt source_location;

  std::string diagnostics;
};

template <typename Diagnostic, typename... Diagnostics>
incorrect_goto_program_exceptiont::incorrect_goto_program_exceptiont(
  std::string message,
  Diagnostic &&diagnostic,
  Diagnostics &&... diagnostics)
  : cprover_exception_baset(std::move(message)),
    source_location(source_locationt::nil()),
    diagnostics(detail::assemble_diagnostics(
      std::forward<Diagnostic>(diagnostic),
      std::forward<Diagnostics>(diagnostics)...))
{
}

template <typename... Diagnostics>
incorrect_goto_program_exceptiont::incorrect_goto_program_exceptiont(
  std::string message,
  source_locationt source_location,
  Diagnostics &&... diagnostics)
  : cprover_exception_baset(std::move(message)),
    source_location(std::move(source_location)),
    diagnostics(
      detail::assemble_diagnostics(std::forward<Diagnostics>(diagnostics)...))
{
}

/// Thrown when we encounter an instruction, parameters to an instruction etc.
/// in a goto program that has some theoretically valid semantics,
/// but that we don't presently have any support for.
class unsupported_operation_exceptiont : public cprover_exception_baset
{
public:
  /// \p message is the unsupported operation causing this fault to occur.
  explicit unsupported_operation_exceptiont(std::string message);
};

/// Thrown when an unexpected error occurs during the analysis (e.g., when the
/// SAT solver returns an error)
class analysis_exceptiont : public cprover_exception_baset
{
public:
  explicit analysis_exceptiont(std::string reason);
};

/// Thrown when we can't handle something in an input source file.
/// For example, if we get C source code that is not syntactically valid
/// or that has type errors.
class invalid_source_file_exceptiont : public cprover_exception_baset
{
public:
  explicit invalid_source_file_exceptiont(std::string reason);
};

#endif // CPROVER_UTIL_EXCEPTION_UTILS_H
