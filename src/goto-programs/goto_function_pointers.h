/*******************************************************************\

Module: Remove Indirect Function Calls

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_GOTO_FUNCTION_POINTERS_H
#define CPROVER_GOTO_FUNCTION_POINTERS_H

#include "goto_functions.h"

// remove indirect function calls
// and replace by case-split
void remove_function_pointers(
  const namespacet &ns,
  goto_functionst &functions);

#endif
