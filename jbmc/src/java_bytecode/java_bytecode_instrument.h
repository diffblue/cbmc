/*******************************************************************\

Module: Instrument codet with assertions/runtime exceptions

Author: Cristina David

Date:   June 2017

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_INSTRUMENT_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_INSTRUMENT_H

#include <string>
#include <vector>

class code_blockt;
class message_handlert;
class symbol_table_baset;
class symbol_tablet;
class symbolt;
class source_locationt;

void java_bytecode_instrument_symbol(
  symbol_table_baset &symbol_table,
  symbolt &symbol,
  const bool throw_runtime_exceptions,
  message_handlert &_message_handler);

void java_bytecode_instrument(
  symbol_tablet &symbol_table,
  const bool throw_runtime_exceptions,
  message_handlert &_message_handler);

void java_bytecode_instrument_uncaught_exceptions(
  code_blockt &init_code,
  const symbolt &exc_symbol,
  const source_locationt &source_location);

extern const std::vector<std::string> exception_needed_classes;

#endif
