/*******************************************************************\

Module: Remove calls to functions without a body

Author: Daniel Poetzl

\*******************************************************************/

/// \file
/// Remove calls to functions without a body

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_CALLS_NOBODY_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_CALLS_NOBODY_H

#include "goto_functions.h"

class remove_calls_nobodyt
{
  typedef goto_functionst::goto_functiont goto_functiont;

public:
  void remove_call_nobody(
    goto_programt &dest,
    goto_programt::targett target,
    const exprt &lhs,
    const exprt::operandst &arguments);

  void remove_calls_nobody(
    goto_programt &goto_program,
    const goto_functionst &goto_functions);

  void remove_calls_nobody(goto_functionst &goto_functions);
};

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_CALLS_NOBODY_H
