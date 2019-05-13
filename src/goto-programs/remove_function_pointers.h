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

#include "collect_function_pointer_targets.h"
#include "remove_const_function_pointers.h"

class goto_functionst;
class goto_programt;
class goto_modelt;
class message_handlert;
class symbol_tablet;

// remove indirect function calls
// and replace by case-split
void remove_function_pointers(
  message_handlert &_message_handler,
  goto_modelt &goto_model,
  bool add_safety_assertion,
  bool only_remove_const_fps=false);

/// Replace all calls to a dynamic function by a case-split over a given set of
///   candidate functions
/// \param _message_handler: a message handler for reporting
/// \param goto_model: model to search for potential functions
/// \param target_map: candidate functions
/// \param add_safety_assertion: check that at least one function matches
/// \param only_remove_const_fps: restrict the pointer remove to const
void remove_function_pointers(
  message_handlert &_message_handler,
  goto_modelt &goto_model,
  const possible_fp_targets_mapt &target_map,
  bool add_safety_assertion,
  bool only_remove_const_fps = false);

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
