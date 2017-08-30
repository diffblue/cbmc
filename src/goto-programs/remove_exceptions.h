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

#define EXC_SUFFIX "#exception_value"

// Removes 'throw x' and CATCH-PUSH/CATCH-POP
// and adds the required instrumentation (GOTOs and assignments)

void remove_exceptions(symbol_tablet &, goto_functionst &);
void remove_exceptions(goto_modelt &);

#endif
