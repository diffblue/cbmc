/*******************************************************************\

Module: Remove Virtual Function (Method) Calls

Author: Daniel Kroening

Date: April 2016

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_VIRTUAL_FUNCTIONS_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_VIRTUAL_FUNCTIONS_H

#include "goto_model.h"

// remove virtual function calls
// and replace by case-split
void remove_virtual_functions(
  goto_modelt &goto_model);

void remove_virtual_functions(
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_VIRTUAL_FUNCTIONS_H
