/*******************************************************************\

Module: Utility functions for code contracts.

Author: Remi Delmas, delmasrd@amazon.com

Date: August 2022

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_INLINING_DECORATOR_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_INLINING_DECORATOR_H

#include <util/irep.h>
#include <util/message.h>

#include <regex>
#include <set>
#include <sstream>

/// Decorator for a \ref message_handlert used during function inlining that
/// collect names of GOTO functions creating warnings and allows to turn
/// inlining warnings into hard errors.
///
/// The decorator intercepts and parses messages sent to the decorated
/// message handler and collects the names of GOTO functions involved in these
/// 4 types warnings:
/// - `recursive call` warnings,
/// - `missing function` warnings,
/// - `not enough arguments` warnings,
/// - `no body for function` warnings.
///
/// For each warning type, the decorator offers:
/// - a method that returns the set of function names that caused the warnings
/// - a method that throws an error in case that set is not empty
///
/// So this decorator allows to inspect the sets of functions involved in
/// warnings to check if the warnings are expected or not, and to turn warnings
/// into hard errors if desired.
///
/// Decorator pattern info: https://en.wikipedia.org/wiki/Decorator_pattern
class inlining_decoratort : public message_handlert
{
private:
  message_handlert &wrapped;

  std::regex no_body_regex;
  std::set<irep_idt> no_body_set;

  void match_no_body_warning(const std::string &message);

  std::regex missing_function_regex;
  std::set<irep_idt> missing_function_set;

  void match_missing_function_warning(const std::string &message);

  std::regex recursive_call_regex;
  std::set<irep_idt> recursive_call_set;

  void match_recursive_call_warning(const std::string &message);

  std::regex not_enough_arguments_regex;
  std::set<irep_idt> not_enough_arguments_set;

  void match_not_enough_arguments_warning(const std::string &message);

  void parse_message(const std::string &message);

public:
  explicit inlining_decoratort(message_handlert &_wrapped);

  /// Throws the given error code if `no body for function`
  /// warnings happend during inlining
  void throw_on_no_body(messaget &log, const int error_code);

  /// Throws the given error code if `recursive call`
  /// warnings happend during inlining
  void throw_on_recursive_calls(messaget &log, const int error_code);

  /// Throws the given error code if `missing function`
  /// warnings happend during inlining
  void throw_on_missing_function(messaget &log, const int error_code);

  /// Throws the given error code if `not enough arguments`
  /// warnings happend during inlining
  void throw_on_not_enough_arguments(messaget &log, const int error_code);

  const std::set<irep_idt> &get_no_body_set() const
  {
    return no_body_set;
  }

  const std::set<irep_idt> &get_missing_function_set() const
  {
    return missing_function_set;
  }

  const std::set<irep_idt> &get_recursive_call_set() const
  {
    return recursive_call_set;
  }

  const std::set<irep_idt> &get_not_enough_arguments_set() const
  {
    return not_enough_arguments_set;
  }

  void print(unsigned level, const std::string &message) override
  {
    parse_message(message);
    wrapped.print(level, message);
  }

  void print(unsigned level, const xmlt &xml) override
  {
    wrapped.print(level, xml);
  }

  void print(unsigned level, const jsont &json) override
  {
    wrapped.print(level, json);
  }

  void print(unsigned level, const structured_datat &data) override
  {
    wrapped.print(level, data);
  }

  void print(
    unsigned level,
    const std::string &message,
    const source_locationt &location) override
  {
    parse_message(message);
    wrapped.print(level, message, location);
    return;
  }

  void flush(unsigned i) override
  {
    return wrapped.flush(i);
  }

  void set_verbosity(unsigned _verbosity)
  {
    wrapped.set_verbosity(_verbosity);
  }

  unsigned get_verbosity() const
  {
    return wrapped.get_verbosity();
  }

  std::size_t get_message_count(unsigned level) const
  {
    return wrapped.get_message_count(level);
  }

  std::string command(unsigned i) const override
  {
    return wrapped.command(i);
  }
};

#endif
