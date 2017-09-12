/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_SKIP_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_SKIP_H

#include "goto_functions.h"

class goto_modelt;

void remove_skip(goto_programt &);
void remove_skip(goto_functionst &);
void remove_skip(goto_modelt &);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_SKIP_H
