/*******************************************************************\

Module: Interpreter for GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Interpreter for GOTO Programs

#ifndef CPROVER_GOTO_PROGRAMS_INTERPRETER_H
#define CPROVER_GOTO_PROGRAMS_INTERPRETER_H

#include <util/message.h>

#include "goto_functions.h"

void interpreter(
  const symbol_tablet &symbol_table,
  const goto_functionst &goto_functions,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_PROGRAMS_INTERPRETER_H
