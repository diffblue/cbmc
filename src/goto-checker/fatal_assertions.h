/*******************************************************************\

Module: Fatal Assertions

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Fatal Assertions

#ifndef CPROVER_GOTO_CHECKER_FATAL_ASSERTIONS_H
#define CPROVER_GOTO_CHECKER_FATAL_ASSERTIONS_H

#include "properties.h"

class goto_functionst;
class goto_trace_storaget;

/// This has two effects.
/// 1. Proven assertions after refuted fatal assertions
///    are marked as UNKNOWN.
/// 2. Refuted assertions are marked as UNKNOWN iff their
///    counterexample trace passes through a non-proven fatal assertion.
void propagate_fatal_assertions(
  propertiest &,
  const goto_trace_storaget &,
  const goto_functionst &);

#endif // CPROVER_GOTO_CHECKER_FATAL_ASSERTIONS_H
