/*******************************************************************\

Module: Goto program validation macros

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_UTIL_VALIDATE_H
#define CPROVER_UTIL_VALIDATE_H

#include <type_traits>

#include "exception_utils.h"
#include "validation_mode.h"

/// This macro takes a condition which denotes a well-formedness criterion on
/// goto programs, expressions, instructions, etc. When invoking the macro, a
/// variable named `vm` of type `const validation_modet` should be in scope. It
/// indicates whether DATA_INVARIANT() is used to check the condition, or if an
/// exception is thrown when the condition does not hold.
#define DATA_CHECK(condition, message)                                         \
  do                                                                           \
  {                                                                            \
    static_assert(                                                             \
      std::is_same<decltype(vm), const validation_modet>::value,               \
      "when invoking the macro DATA_CHECK(), a variable named `vm` of type "   \
      "`const validation_modet` should be in scope which indicates the "       \
      "validation mode (see `validate.h`");                                    \
    switch(vm)                                                                 \
    {                                                                          \
    case validation_modet::INVARIANT:                                          \
      DATA_INVARIANT(condition, message);                                      \
      break;                                                                   \
    case validation_modet::EXCEPTION:                                          \
      if(!(condition))                                                         \
        throw incorrect_goto_program_exceptiont(message);                      \
      break;                                                                   \
    }                                                                          \
  } while(0)

#define DATA_CHECK_WITH_DIAGNOSTICS(condition, message, ...)                   \
  do                                                                           \
  {                                                                            \
    static_assert(                                                             \
      std::is_same<decltype(vm), const validation_modet>::value,               \
      "when invoking the macro DATA_CHECK_WITH_DIAGNOSTICS(), a variable "     \
      "named `vm` of type `const validation_modet` should be in scope which "  \
      "indicates the validation mode (see `validate.h`");                      \
    switch(vm)                                                                 \
    {                                                                          \
    case validation_modet::INVARIANT:                                          \
      DATA_INVARIANT_WITH_DIAGNOSTICS(condition, message, __VA_ARGS__);        \
      break;                                                                   \
    case validation_modet::EXCEPTION:                                          \
      if(!(condition))                                                         \
        throw incorrect_goto_program_exceptiont(message, __VA_ARGS__);         \
      break;                                                                   \
    }                                                                          \
  } while(0)

#endif /* CPROVER_UTIL_VALIDATE_H */
