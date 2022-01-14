/*******************************************************************\

Module: Remove calls to functions without a body

Author: Daniel Poetzl

\*******************************************************************/

/// \file
/// Remove calls to functions without a body

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_CALLS_NO_BODY_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_CALLS_NO_BODY_H

#include "goto_program.h"

class goto_functionst;
class message_handlert;

class remove_calls_no_bodyt
{
protected:
  bool is_opaque_function_call(
    const goto_programt::const_targett target,
    const goto_functionst &goto_functions);

  void remove_call_no_body(
    goto_programt &dest,
    goto_programt::targett target,
    const exprt &lhs,
    const exprt::operandst &arguments);

public:
  void operator()(
    goto_programt &goto_program,
    const goto_functionst &goto_functions,
    message_handlert &);

  void operator()(goto_functionst &goto_functions, message_handlert &);
};

#define OPT_REMOVE_CALLS_NO_BODY "(remove-calls-no-body)"

#define HELP_REMOVE_CALLS_NO_BODY                                              \
  " --remove-calls-no-body       remove calls to functions without a body\n"

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_CALLS_NO_BODY_H
