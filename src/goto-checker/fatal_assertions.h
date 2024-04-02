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
/// are marked as UNKNOWN.
void propagate_fatal_assertions(propertiest &, const goto_functionst &);

#endif // CPROVER_GOTO_CHECKER_FATAL_ASSERTIONS_H
