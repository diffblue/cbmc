/*******************************************************************\

Module: Concrete Symbolic Transformer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SYMEX_H
#define CPROVER_SYMEX_H

#include <util/options.h>
#include <path-symex/locs.h>

#include "state.h"

// Transforms a state by executing a thread (state.current_thread).
// May occasionally yield more than one next state
// (branches), which are put into "further_states".

void symex(
  const locst &locs,
  statet &state,
  std::list<statet> &further_states,
  const namespacet &ns,
  const optionst &options);

// Transform a state by executing the path beginning
// at the node of the current state to node.
void symex(
  const locst &locs,
  statet &state,
  const namespacet &ns,
  const optionst &options);


#endif
