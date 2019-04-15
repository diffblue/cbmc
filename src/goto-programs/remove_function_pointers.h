/*******************************************************************\

Module: Remove Indirect Function Calls

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

/// \file
/// Remove Indirect Function Calls

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_FUNCTION_POINTERS_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_FUNCTION_POINTERS_H

#include <util/irep.h>

#include <map>

#include "remove_const_function_pointers.h"

class goto_functionst;
class goto_programt;
class goto_modelt;
class message_handlert;
class symbol_tablet;

using possible_fp_targetst = remove_const_function_pointerst::functionst;
using possible_fp_targets_mapt = std::map<irep_idt, possible_fp_targetst>;

possible_fp_targets_mapt get_function_pointer_targets(
  message_handlert &message_handler,
  goto_modelt &goto_model);

// remove indirect function calls
// and replace by case-split
void remove_function_pointers(
  message_handlert &_message_handler,
  goto_modelt &goto_model,
  bool add_safety_assertion,
  bool only_remove_const_fps=false);

void remove_function_pointers(
  message_handlert &_message_handler,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  bool add_safety_assertion,
  bool only_remove_const_fps=false);

bool remove_function_pointers(
  message_handlert &_message_handler,
  symbol_tablet &symbol_table,
  const goto_functionst &goto_functions,
  goto_programt &goto_program,
  const irep_idt &function_id,
  bool add_safety_assertion,
  bool only_remove_const_fps = false);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_FUNCTION_POINTERS_H
