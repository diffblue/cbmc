/*******************************************************************\

Module: Remove function exceptional returns

Author: Cristina David

Date:   December 2016

\*******************************************************************/

/// \file
/// Remove function exceptional returns

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_EXCEPTIONS_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_EXCEPTIONS_H

#include <goto-programs/goto_model.h>

#define INFLIGHT_EXCEPTION_VARIABLE_BASENAME "@inflight_exception"
#define INFLIGHT_EXCEPTION_VARIABLE_NAME \
  "java::" INFLIGHT_EXCEPTION_VARIABLE_BASENAME

// Removes 'throw x' and CATCH-PUSH/CATCH-POP
// and adds the required instrumentation (GOTOs and assignments)

enum class remove_exceptions_typest
{
  REMOVE_ADDED_INSTANCEOF,
  DONT_REMOVE_INSTANCEOF,
};

void remove_exceptions(
  goto_modelt &goto_model,
  remove_exceptions_typest type =
    remove_exceptions_typest::DONT_REMOVE_INSTANCEOF);

#endif
