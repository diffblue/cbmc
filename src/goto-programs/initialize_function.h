/*******************************************************************\

Module: Initialize Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Defines INITIALIZE_FUNCTION, the name of the function that initializes
/// all non-function symbols with static lifetime.

#ifndef CPROVER_GOTO_PROGRAMS_INITIALIZE_FUNCTION_H
#define CPROVER_GOTO_PROGRAMS_INITIALIZE_FUNCTION_H

#include <util/cprover_prefix.h>

#define INITIALIZE_FUNCTION CPROVER_PREFIX "initialize"

#endif // CPROVER_GOTO_PROGRAMS_INITIALIZE_FUNCTION_H
