/*******************************************************************\

Module: Interpreter for GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_INTERPRETER_H
#define CPROVER_INTERPRETER_H

#include "goto_functions.h"

void interpreter(
  const contextt &context,
  const goto_functionst &goto_functions);

#endif
