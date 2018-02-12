/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Language Conversion

#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_METHOD_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_METHOD_H

#include <util/symbol_table.h>
#include <util/message.h>
#include "java_string_library_preprocess.h"

#include "java_bytecode_parse_tree.h"
#include <java_bytecode/ci_lazy_methods_needed.h>

class class_hierarchyt;

void java_bytecode_initialize_parameter_names(
  symbolt &method_symbol,
  const java_bytecode_parse_treet::methodt::local_variable_tablet
    &local_variable_table,
  symbol_table_baset &symbol_table);

void java_bytecode_convert_method(
  const symbolt &class_symbol,
  const java_bytecode_parse_treet::methodt &,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler,
  size_t max_array_length,
  optionalt<ci_lazy_methods_neededt> needed_lazy_methods,
  java_string_library_preprocesst &string_preprocess,
  const class_hierarchyt &class_hierarchy);

void java_bytecode_convert_method_lazy(
  const symbolt &class_symbol,
  const irep_idt &method_identifier,
  const java_bytecode_parse_treet::methodt &,
  symbol_tablet &symbol_table,
  message_handlert &);

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_METHOD_H
