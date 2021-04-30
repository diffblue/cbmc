/*******************************************************************\

Module: Generate Equation using Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Generate Equation using Symbolic Execution

#ifndef CPROVER_GOTO_SYMEX_PRECONDITION_H
#define CPROVER_GOTO_SYMEX_PRECONDITION_H

#include "goto-programs/goto_program.h"

class exprt;
class namespacet;
class symex_target_equationt;
class value_setst;

void precondition(
  const namespacet &ns,
  value_setst &value_sets,
  const goto_programt::const_targett target,
  const symex_target_equationt &equation,
  const class goto_symex_statet &s,
  exprt &dest);

#endif // CPROVER_GOTO_SYMEX_PRECONDITION_H
