/*******************************************************************\

Module: Exception helper utilities

Author: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com

\*******************************************************************/

#include "exception_utils.h"

#include <utility>

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

deserialization_exceptiont::deserialization_exceptiont(std::string message)
  : message(std::move(message))
{}

std::string deserialization_exceptiont::what() const noexcept {
  return message;
}
