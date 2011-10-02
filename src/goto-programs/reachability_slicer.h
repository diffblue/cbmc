/*******************************************************************\

Module: Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_SLICER_H
#define CPROVER_GOTO_PROGRAMS_SLICER_H

#include "goto_functions.h"

void reachability_slicer(goto_functionst &goto_functions);
void reachability_slicer(goto_programt &goto_program);

#endif
