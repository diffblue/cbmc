/*******************************************************************\

Module: Remove Indirect Function Calls

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_GOTO_FUNCTION_POINTERS_H
#define CPROVER_GOTO_FUNCTION_POINTERS_H

#include "goto_model.h"

// remove indirect function calls
// and replace by case-split
void remove_function_pointers(
  goto_modelt &goto_model,
  bool add_safety_assertion);

void remove_function_pointers(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  bool add_safety_assertion);

#endif
