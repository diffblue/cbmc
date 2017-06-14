/*******************************************************************\

Module: Remove function definition

Author: Michael Tautschnig

Date: April 2017

\*******************************************************************/

/// \file
/// Remove function definition

#ifndef CPROVER_GOTO_INSTRUMENT_REMOVE_FUNCTION_H
#define CPROVER_GOTO_INSTRUMENT_REMOVE_FUNCTION_H

#include <list>
#include <string>

#include <util/irep.h>

class goto_functionst;
class message_handlert;
class symbol_tablet;

void remove_function(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  const irep_idt &identifier,
  message_handlert &message_handler);

void remove_functions(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  const std::list<std::string> &names,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_INSTRUMENT_REMOVE_FUNCTION_H
