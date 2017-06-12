/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Language Conversion

#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_CLASS_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_CLASS_H

#include <util/symbol_table.h>
#include <util/message.h>

#include "java_bytecode_parse_tree.h"
#include "java_bytecode_language.h"

bool java_bytecode_convert_class(
  const java_bytecode_parse_treet &parse_tree,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  size_t max_array_length,
  lazy_methodst &,
  lazy_methods_modet,
  java_string_library_preprocesst &string_preprocess);

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_CLASS_H
