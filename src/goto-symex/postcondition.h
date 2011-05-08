/*******************************************************************\

Module: Generate Equation using Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_POSTCONDITION_H
#define CPROVER_GOTO_SYMEX_POSTCONDITION_H

#include <pointer-analysis/value_sets.h>

#include "symex_target_equation.h"

void postcondition(
  const namespacet &ns,
  const value_setst &value_sets,
  const symex_target_equationt &equation,
  const class goto_symex_statet &s,
  exprt &dest);

#endif
