/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_SKIP_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_SKIP_H

#include "goto_functions.h"

void remove_skip(goto_programt &goto_program, bool remove_labeled=false);
void remove_skip(goto_functionst &goto_functions, bool remove_labled=false);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_SKIP_H
