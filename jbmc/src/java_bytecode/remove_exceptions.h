/*******************************************************************\

Module: Remove function exceptional returns

Author: Cristina David

Date:   December 2016

\*******************************************************************/

/// \file
/// Remove function exceptional returns

#ifndef CPROVER_JAVA_BYTECODE_REMOVE_EXCEPTIONS_H
#define CPROVER_JAVA_BYTECODE_REMOVE_EXCEPTIONS_H

#include <goto-programs/class_hierarchy.h>
#include <goto-programs/goto_model.h>

#include <util/message.h>

#define INFLIGHT_EXCEPTION_VARIABLE_BASENAME "@inflight_exception"
#define INFLIGHT_EXCEPTION_VARIABLE_NAME \
  "java::" INFLIGHT_EXCEPTION_VARIABLE_BASENAME

/// Removes 'throw x' and CATCH-PUSH/CATCH-POP
/// and adds the required instrumentation (GOTOs and assignments)
/// This introduces instanceof expressions.
void remove_exceptions_using_instanceof(
  const irep_idt &function_identifier,
  goto_programt &,
  symbol_table_baset &,
  message_handlert &);

/// Removes 'throw x' and CATCH-PUSH/CATCH-POP
/// and adds the required instrumentation (GOTOs and assignments)
/// This introduces instanceof expressions.
void remove_exceptions_using_instanceof(goto_modelt &, message_handlert &);

/// Removes 'throw x' and CATCH-PUSH/CATCH-POP
/// and adds the required instrumentation (GOTOs and assignments)
/// This does not introduce instanceof expressions.
void remove_exceptions(
  const irep_idt &function_identifier,
  goto_programt &,
  symbol_table_baset &,
  const class_hierarchyt &,
  message_handlert &);

/// Removes 'throw x' and CATCH-PUSH/CATCH-POP
/// and adds the required instrumentation (GOTOs and assignments)
/// This does not introduce instanceof expressions.
void remove_exceptions(
  goto_modelt &,
  const class_hierarchyt &,
  message_handlert &);

#endif
