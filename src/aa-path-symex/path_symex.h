/*******************************************************************\

Module: Concrete Symbolic Transformer

Author: Daniel Kroening, kroening@kroening.com
        Alex Horn, alex.horn@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_PATH_SYMEX_H
#define CPROVER_PATH_SYMEX_H

#include "locs.h"
#include "path_symex_state.h"

// Transform a state by executing a single statement.
// May occasionally yield more than one successor state
// (branches, function calls with ternary operator),
// which are put into "further_states".

// \pre: "!further_states.empty()" because "state" must
//       be stored inside "further_states"
void path_symex(
  path_symex_statet &state,
  std::list<path_symex_statet> &further_states);

// Transform a state by executing a single statement.
// Will fail if there is more than one successor state.
void path_symex(path_symex_statet &state);

// Transforms a state by executing a goto statement;
// the 'taken' argument indicates which way.
void path_symex_goto(
  path_symex_statet &state,
  bool taken);

// Transforms a state by executing an assertion statement;
// it is enforced that the assertion fails.
void path_symex_assert_fail(
  path_symex_statet &state);

#endif
