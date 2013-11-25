/*******************************************************************\

Module: Generate Equation using Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_PRECONDITION_H
#define CPROVER_GOTO_SYMEX_PRECONDITION_H

#include <pointer-analysis/value_sets.h>

#include "symex_target_equation.h"

void precondition(
  const namespacet &ns,
  value_setst &value_sets,
  const goto_programt::const_targett target,
  const symex_target_equationt &equation,
  const class goto_symex_statet &s,
  exprt &dest);

#endif
