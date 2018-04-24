/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_SKIP_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_SKIP_H

#include "goto_program.h"

class goto_functionst;
class goto_modelt;

bool is_skip(
  const goto_programt &,
  goto_programt::const_targett,
  bool ignore_labels = false);
void remove_skip(goto_programt &);
void remove_skip(goto_functionst &);
void remove_skip(goto_modelt &);

void remove_skip(
  goto_programt &goto_program,
  goto_programt::targett begin,
  const goto_programt::targett end);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_SKIP_H
