/*******************************************************************\

Module: Generate Equation using Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Generate Equation using Symbolic Execution

#ifndef CPROVER_GOTO_SYMEX_POSTCONDITION_H
#define CPROVER_GOTO_SYMEX_POSTCONDITION_H

class exprt;
class namespacet;
class symex_target_equationt;
class value_setst;

void postcondition(
  const namespacet &ns,
  const value_setst &value_sets,
  const symex_target_equationt &equation,
  const class goto_symex_statet &s,
  exprt &dest);

#endif // CPROVER_GOTO_SYMEX_POSTCONDITION_H
