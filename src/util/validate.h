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
/// goto programs, expressions, instructions, etc. The first parameter should be
/// of type `validate_modet` and indicates whether DATA_INVARIANT() is used to
/// check the condition, or if an exception is thrown when the condition does
/// not hold.
#define DATA_CHECK(vm, condition, message)                                     \
  do                                                                           \
  {                                                                            \
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

#define DATA_CHECK_WITH_DIAGNOSTICS(vm, condition, message, ...)               \
  do                                                                           \
  {                                                                            \
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
