/*******************************************************************\

Module: Remove Indirect Function Calls

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

/// \file
/// Remove Indirect Function Calls

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_FUNCTION_POINTERS_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_FUNCTION_POINTERS_H

#include "goto_program.h"

#include <unordered_set>

class goto_functionst;
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

/// Replace a call to a dynamic function at location
/// target in the given goto-program by a case-split
/// over a given set of functions
/// \param message_handler: Message handler to print warnings
/// \param symbol_table: Symbol table
/// \param goto_program: The goto program that contains target
/// \param function_id: Name of function containing the target
/// \param target: location with function call with function pointer
/// \param functions: The set of functions to consider
/// \param add_safety_assertion: Iff true, include an assertion that the
//         pointer matches one of the candidate functions
void remove_function_pointer(
  message_handlert &message_handler,
  symbol_tablet &symbol_table,
  goto_programt &goto_program,
  const irep_idt &function_id,
  goto_programt::targett target,
  const std::unordered_set<symbol_exprt, irep_hash> &functions,
  const bool add_safety_assertion);

/// Returns true iff \p call_type can be converted to produce a function call of
/// the same type as \p function_type.
bool function_is_type_compatible(
  bool return_value_used,
  const code_typet &call_type,
  const code_typet &function_type,
  const namespacet &ns);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_FUNCTION_POINTERS_H
