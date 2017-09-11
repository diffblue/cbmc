/*******************************************************************\

Module: Interpreter for GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Interpreter for GOTO Programs

#ifndef CPROVER_GOTO_PROGRAMS_INTERPRETER_H
#define CPROVER_GOTO_PROGRAMS_INTERPRETER_H

#include <util/message.h>

#include "goto_model.h"

void interpreter(
  const goto_modelt &,
  message_handlert &);

#endif // CPROVER_GOTO_PROGRAMS_INTERPRETER_H
