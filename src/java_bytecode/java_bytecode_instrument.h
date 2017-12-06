/*******************************************************************\

Module: Instrument codet with assertions/runtime exceptions

Author: Cristina David

Date:   June 2017

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_INSTRUMENT_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_INSTRUMENT_H

#include <util/symbol_table.h>
#include <util/message.h>
#include <util/irep.h>

void java_bytecode_instrument_symbol(
  symbol_table_baset &symbol_table,
  symbolt &symbol,
  const bool throw_runtime_exceptions,
  message_handlert &_message_handler);

void java_bytecode_instrument(
  symbol_tablet &symbol_table,
  const bool throw_runtime_exceptions,
  message_handlert &_message_handler);

extern const std::vector<irep_idt> exception_needed_classes;

#endif
