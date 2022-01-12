/*******************************************************************\

Module: Remove initializations of unused global variables

Author: Daniel Poetzl

Date:   December 2016

\*******************************************************************/

/// \file
/// Remove initializations of unused global variables

#ifndef CPROVER_GOTO_PROGRAMS_SLICE_GLOBAL_INITS_H
#define CPROVER_GOTO_PROGRAMS_SLICE_GLOBAL_INITS_H

#include <util/exception_utils.h>

class goto_modelt;
class message_handlert;

class user_input_error_exceptiont : public cprover_exception_baset
{
public:
  explicit user_input_error_exceptiont(std::string message)
    : message(std::move(message))
  {
  }

  std::string what() const override
  {
    return message;
  }

private:
  std::string message;
};

/// Remove initialization of global variables that are not used in any function
/// reachable from the entry point of \p goto_model.
/// Warnings are reported via \p message_handler.
void slice_global_inits(
  goto_modelt &goto_model,
  message_handlert &message_handler);

#endif
