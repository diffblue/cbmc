/*******************************************************************\

Module: Exception helper utilities

Author: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_EXCEPTION_UTILS_H
#define CPROVER_UTIL_EXCEPTION_UTILS_H

#include <string>

class invalid_user_input_exceptiont
{
  std::string reason;
  std::string option;
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
