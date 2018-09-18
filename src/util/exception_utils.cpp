#include <utility>

#include <utility>

/*******************************************************************\

Module: Exception helper utilities

Author: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com

\*******************************************************************/

#include "exception_utils.h"

std::string invalid_user_input_exceptiont::what() const noexcept
{
  std::string res;
  res += "\nInvalid User Input\n";
  res += "Option: " + option + "\n";
  res += "Reason: " + reason;
  // Print an optional correct usage message assuming correct input parameters have been passed
  res += correct_input + "\n";
  return res;
}

incorrect_goto_program_exceptiont::incorrect_goto_program_exceptiont(
  std::string message,
  source_locationt source_location) noexcept
  : message(std::move(message)), source_location(std::move(source_location))
{
}

std::string incorrect_goto_program_exceptiont::what() const noexcept
{
  return message + "(at: " + source_location.as_string() + ")";
}
