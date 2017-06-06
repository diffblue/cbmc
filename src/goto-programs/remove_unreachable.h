/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_UNREACHABLE_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_UNREACHABLE_H

#include "goto_functions.h"

void remove_unreachable(goto_programt &goto_program);
void remove_unreachable(goto_functionst &goto_functions);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_UNREACHABLE_H
