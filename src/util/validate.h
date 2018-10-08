/*******************************************************************\

Module: Goto program validation

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_UTIL_VALIDATE_H
#define CPROVER_UTIL_VALIDATE_H

#include <type_traits>

#include "exception_utils.h"
#include "invariant.h"
#include "irep.h"

enum class validation_modet
{
  INVARIANT,
  EXCEPTION
};

#define GET_FIRST(A, ...) A

/// This macro takes a condition which denotes a well-formedness criterion on
/// goto programs, expressions, instructions, etc. Based on the value of the
/// variable vm (the validation mode), it either uses DATA_INVARIANT() to check
/// those conditions, or throws an exception when a condition does not hold.
#define DATA_CHECK(condition, message)                                         \
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

#define DATA_CHECK_WITH_DIAGNOSTICS(condition, message, ...)                   \
  do                                                                           \
  {                                                                            \
    switch(vm)                                                                 \
    {                                                                          \
    case validation_modet::INVARIANT:                                          \
      DATA_INVARIANT_WITH_DIAGNOSTICS(condition, message, __VA_ARGS__);        \
      break;                                                                   \
    case validation_modet::EXCEPTION:                                          \
      if(!(condition))                                                         \
        throw incorrect_goto_program_exceptiont(                               \
          message, GET_FIRST(__VA_ARGS__, dummy));                             \
      break;                                                                   \
    }                                                                          \
  } while(0)

#endif /* CPROVER_UTIL_VALIDATE_H */
