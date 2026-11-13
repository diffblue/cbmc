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

/// Proven assertions after refuted fatal assertions
/// are marked as UNKNOWN. This includes code that runs after a return from
/// the function holding a refuted fatal assertion, and, in multi-threaded
/// programs, the code of all threads.
void propagate_fatal_assertions(propertiest &, const goto_functionst &);

#endif // CPROVER_GOTO_CHECKER_FATAL_ASSERTIONS_H
