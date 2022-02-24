/*******************************************************************\

Module: Exception helper utilities

Author: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com

\*******************************************************************/

#include "exception_utils.h"
#include <utility>

std::string cprover_exception_baset::what() const
{
  return reason;
}

std::string invalid_command_line_argument_exceptiont::what() const
{
  std::string res;
  res += "Invalid User Input";
  res += "\nOption: " + option;
  res += "\nReason: " + reason;
  // Print an optional correct usage message assuming correct input parameters have been passed
  if(!correct_input.empty())
  {
    res += "\nSuggestion: " + correct_input;
  }
  return res;
}

invalid_command_line_argument_exceptiont::
  invalid_command_line_argument_exceptiont(
    std::string reason,
    std::string option,
    std::string correct_input)
  : cprover_exception_baset(std::move(reason)),
    option(std::move(option)),
    correct_input(std::move(correct_input))
{
}

system_exceptiont::system_exceptiont(std::string message)
  : cprover_exception_baset(std::move(message))
{
}

deserialization_exceptiont::deserialization_exceptiont(std::string message)
  : cprover_exception_baset(std::move(message))
{
}

incorrect_goto_program_exceptiont::incorrect_goto_program_exceptiont(
  std::string message)
  : cprover_exception_baset(std::move(message)),
    source_location(source_locationt::nil())
{
}

std::string incorrect_goto_program_exceptiont::what() const
{
  std::string ret(reason);

  if(!source_location.is_nil())
    ret += " (at: " + source_location.as_string() + ")";

  if(!diagnostics.empty())
    ret += "\n" + diagnostics;

  return ret;
}

unsupported_operation_exceptiont::unsupported_operation_exceptiont(
  std::string message)
  : cprover_exception_baset(std::move(message))
{
}

analysis_exceptiont::analysis_exceptiont(std::string reason)
  : cprover_exception_baset(std::move(reason))
{
}

invalid_input_exceptiont::invalid_input_exceptiont(std::string reason)
  : cprover_exception_baset(std::move(reason))
{
}

invalid_source_file_exceptiont::invalid_source_file_exceptiont(
  std::string reason)
  : cprover_exception_baset(std::move(reason))
{
}
