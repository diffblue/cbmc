/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_METHOD_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_METHOD_H

#include <util/symbol_table.h>
#include <util/message.h>
#include <util/safe_pointer.h>

#include "java_bytecode_parse_tree.h"
#include "ci_lazy_methods.h"

class class_hierarchyt;

void java_bytecode_convert_method(
  const symbolt &class_symbol,
  const java_bytecode_parse_treet::methodt &,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  size_t max_array_length,
  bool throw_runtime_exceptions,
  safe_pointer<ci_lazy_methodst> lazy_methods);

inline void java_bytecode_convert_method(
  const symbolt &class_symbol,
  const java_bytecode_parse_treet::methodt &method,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  size_t max_array_length,
  bool throw_runtime_exceptions)
{
  java_bytecode_convert_method(
    class_symbol,
    method,
    symbol_table,
    message_handler,
    max_array_length,
    throw_runtime_exceptions,
    safe_pointer<ci_lazy_methodst>::create_null());
}

void java_bytecode_convert_method_lazy(
  const symbolt &class_symbol,
  const irep_idt &method_identifier,
  const java_bytecode_parse_treet::methodt &,
  symbol_tablet &symbol_table);

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_METHOD_H
