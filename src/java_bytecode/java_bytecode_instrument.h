/*******************************************************************\

Module: Instrument codet with assertions/runtime exceptions

Author: Cristina David

Date:   June 2017

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_INSTRUMENT_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_INSTRUMENT_H

void java_bytecode_instrument_symbol(
  symbol_tablet &symbol_table,
  symbolt &symbol,
  const bool throw_runtime_exceptions,
  message_handlert &_message_handler);

void java_bytecode_instrument(
  symbol_tablet &symbol_table,
  const bool throw_runtime_exceptions,
  message_handlert &_message_handler);

#endif
