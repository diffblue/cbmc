/*******************************************************************\

Module: Exception helper utilities

Author: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com

\*******************************************************************/

#include "exception_utils.h"
#include <utility>

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
  : reason(std::move(reason)),
    option(std::move(option)),
    correct_input(std::move(correct_input))
{
}

system_exceptiont::system_exceptiont(std::string message)
  : message(std::move(message))
{
}

std::string system_exceptiont::what() const
{
  return message;
}

deserialization_exceptiont::deserialization_exceptiont(std::string message)
  : message(std::move(message))
{
}

std::string deserialization_exceptiont::what() const
{
  return message;
}

incorrect_goto_program_exceptiont::incorrect_goto_program_exceptiont(
  std::string message,
  source_locationt source_location)
  : message(std::move(message)), source_location(std::move(source_location))
{
}

std::string incorrect_goto_program_exceptiont::what() const
{
  return message + " (at: " + source_location.as_string() + ")";
}

unsupported_operation_exceptiont::unsupported_operation_exceptiont(
  std::string message)
  : message(std::move(message))
{
}

std::string unsupported_operation_exceptiont::what() const
{
  return message;
}

analysis_exceptiont::analysis_exceptiont(std::string reason)
  : reason(std::move(reason))
{
}

std::string analysis_exceptiont::what() const
{
  return reason;
}

invalid_source_file_exceptiont::invalid_source_file_exceptiont(
  std::string reason)
  : reason(std::move(reason))
{
}

std::string invalid_source_file_exceptiont::what() const
{
  return reason;
}
