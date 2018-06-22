/*******************************************************************\

Module: Remove Instance-of Operators

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Remove Instance-of Operators

#ifndef CPROVER_JAVA_BYTECODE_REMOVE_INSTANCEOF_H
#define CPROVER_JAVA_BYTECODE_REMOVE_INSTANCEOF_H

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_model.h>

#include <util/message.h>
#include <util/symbol_table.h>

void remove_instanceof(
  goto_programt::targett target,
  goto_programt &goto_program,
  symbol_table_baset &symbol_table,
  message_handlert &);

void remove_instanceof(
  goto_functionst::goto_functiont &function,
  symbol_table_baset &symbol_table,
  message_handlert &);

void remove_instanceof(
  goto_functionst &goto_functions,
  symbol_table_baset &symbol_table,
  message_handlert &);

void remove_instanceof(goto_modelt &model, message_handlert &);

#endif
