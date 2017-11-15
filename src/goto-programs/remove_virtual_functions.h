/*******************************************************************\

Module: Remove Virtual Function (Method) Calls

Author: Daniel Kroening

Date: April 2016

\*******************************************************************/

/// \file
/// Remove Virtual Function (Method) Calls

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

/// Specifies remove_virtual_function's behaviour when the actual supplied
/// parameter does not match any of the possible callee types
enum class virtual_dispatch_fallback_actiont
{
  /// When no callee type matches, call the last passed function, which
  /// is expected to be some safe default:
  CALL_LAST_FUNCTION,
  /// When no callee type matches, ASSUME false, thus preventing any complete
  /// trace from using this path.
  ASSUME_FALSE
};

class dispatch_table_entryt
{
 public:
  dispatch_table_entryt() = default;
  explicit dispatch_table_entryt(const irep_idt &_class_id) :
    class_id(_class_id)
  {}

  symbol_exprt symbol_expr;
  irep_idt class_id;
};

typedef std::vector<dispatch_table_entryt> dispatch_table_entriest;

void remove_virtual_function(
  goto_modelt &goto_model,
  goto_programt &goto_program,
  goto_programt::targett instruction,
  const dispatch_table_entriest &dispatch_table,
  virtual_dispatch_fallback_actiont fallback_action);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_VIRTUAL_FUNCTIONS_H
