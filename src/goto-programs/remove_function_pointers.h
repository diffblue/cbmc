/*******************************************************************\

Module: Remove Indirect Function Calls

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_FUNCTION_POINTERS_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_FUNCTION_POINTERS_H

#include "goto_model.h"

// remove indirect function calls
// and replace by case-split
void remove_function_pointers(
  message_handlert &_message_handler,
  goto_modelt &goto_model,
  bool add_safety_assertion);

void remove_function_pointers(
  message_handlert &_message_handler,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  bool add_safety_assertion);

bool remove_function_pointers(
  message_handlert &_message_handler,
  symbol_tablet &symbol_table,
  const goto_functionst &goto_functions,
  goto_programt &goto_program,
  bool add_safety_assertion);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_FUNCTION_POINTERS_H
