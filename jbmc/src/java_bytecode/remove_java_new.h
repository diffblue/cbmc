/*******************************************************************\

Module: Remove Java New Operators

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Remove Java New Operators

#ifndef CPROVER_JAVA_BYTECODE_REMOVE_JAVA_NEW_H
#define CPROVER_JAVA_BYTECODE_REMOVE_JAVA_NEW_H

#include <util/symbol_table.h>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_model.h>

class message_handlert;

void remove_java_new(
  const irep_idt &function_identifier,
  goto_programt::targett target,
  goto_programt &goto_program,
  symbol_table_baset &symbol_table,
  message_handlert &_message_handler);

void remove_java_new(
  const irep_idt &function_identifier,
  goto_functionst::goto_functiont &function,
  symbol_table_baset &symbol_table,
  message_handlert &_message_handler);

void remove_java_new(
  goto_functionst &goto_functions,
  symbol_table_baset &symbol_table,
  message_handlert &_message_handler);

void remove_java_new(goto_modelt &model, message_handlert &_message_handler);

#endif // CPROVER_JAVA_BYTECODE_REMOVE_JAVA_NEW_H
