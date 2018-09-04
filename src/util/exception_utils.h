/*******************************************************************\

Module: Exception helper utilities

Author: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_EXCEPTION_UTILS_H
#define CPROVER_UTIL_EXCEPTION_UTILS_H

#include <string>

class invalid_user_input_exceptiont
{
  /// The reason this exception was generated.
  std::string reason;
  /// The full command line option (not the argument) that got
  /// erroneous input.
  std::string option;
  /// In case we have samples of correct input to the option.
  std::string correct_input;

public:
  invalid_user_input_exceptiont(
    std::string reason,
    std::string option,
    std::string correct_input = "")
    : reason(reason), option(option), correct_input(correct_input)
  {
  }

  std::string what() const noexcept;
};

#endif // CPROVER_UTIL_EXCEPTION_UTILS_H
