/*******************************************************************\

Module: Concrete Symbolic Transformer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PATH_SYMEX_H
#define CPROVER_PATH_SYMEX_H

#include "locs.h"
#include "path_symex_state.h"

// Transform a state by executing a single statement.
// May occasionally yield more than one successor state
// (e.g., branches, the trinary operator, etc),
// which are put into "further_states".

void path_symex(
  path_symex_statet &state,
  std::list<path_symex_statet> &further_states);

// Transforms a state by executing a goto statement;
// the 'taken' argument indicates which way.
void path_symex_goto(
  path_symex_statet &state,
  bool taken);

#endif
