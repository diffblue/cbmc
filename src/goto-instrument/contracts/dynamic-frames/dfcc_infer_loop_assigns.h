/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Infer a set of assigns clause targets for a natural loop.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_INFER_LOOP_ASSIGNS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_INFER_LOOP_ASSIGNS_H

#include <analyses/local_may_alias.h>
#include <goto-instrument/loop_utils.h>
class source_locationt;
class messaget;
class namespacet;

// \brief Infer assigns clause targets for a loop from its instructions and a
// may alias analysis at the function level.
assignst dfcc_infer_loop_assigns(
  const local_may_aliast &local_may_alias,
  const loopt &loop_instructions,
  const source_locationt &loop_head_location,
  const namespacet &ns);

#endif
