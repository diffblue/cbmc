/*******************************************************************\

Module: Remove Virtual Function (Method) Calls

Author: Daniel Kroening

Date: April 2016

\*******************************************************************/

/// \file
/// Functions for replacing virtual function call with a static
/// function calls in functions, groups of functions and goto programs

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_VIRTUAL_FUNCTIONS_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_VIRTUAL_FUNCTIONS_H

#include <util/std_expr.h>

#include "class_hierarchy.h"
#include "goto_program.h"

class goto_functionst;
class goto_model_functiont;
class goto_modelt;
class symbol_table_baset;

void remove_virtual_functions(
  goto_modelt &goto_model);

void remove_virtual_functions(
  const symbol_table_baset &symbol_table,
  goto_functionst &goto_functions);

/// Remove virtual functions from one function.
/// May change the location numbers in `function`.
/// \param function: function from which virtual functions should be converted
///   to explicit dispatch tables.
void remove_virtual_functions(goto_model_functiont &function);

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
typedef std::map<irep_idt, dispatch_table_entryt> dispatch_table_entries_mapt;

goto_programt::targett remove_virtual_function(
  goto_modelt &goto_model,
  goto_programt &goto_program,
  goto_programt::targett instruction,
  const dispatch_table_entriest &dispatch_table,
  virtual_dispatch_fallback_actiont fallback_action);

goto_programt::targett remove_virtual_function(
  symbol_tablet &symbol_table,
  goto_programt &goto_program,
  goto_programt::targett instruction,
  const dispatch_table_entriest &dispatch_table,
  virtual_dispatch_fallback_actiont fallback_action);

/// Given a function expression representing a virtual method of a class,
/// the function computes all overridden methods of that virtual method.
/// \param function: The virtual function expression for which the overridden
///   methods will be searched for.
/// \param symbol_table: A symbol table.
/// \param class_hierarchy: A class hierarchy.
/// \param [out] overridden_functions: Output collection into which all
///   overridden functions will be stored.
void collect_virtual_function_callees(
  const exprt &function,
  const symbol_tablet &symbol_table,
  const class_hierarchyt &class_hierarchy,
  dispatch_table_entriest &overridden_functions);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_VIRTUAL_FUNCTIONS_H
