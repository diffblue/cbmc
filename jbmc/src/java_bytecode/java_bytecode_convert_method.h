/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Language Conversion

#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_METHOD_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_METHOD_H

#include "ci_lazy_methods_needed.h"
#include "java_bytecode_convert_method_class.h"
#include "java_bytecode_parse_tree.h"
#include "java_string_library_preprocess.h"

#include <util/message.h>
#include <util/symbol_table.h>

class class_hierarchyt;
class prefix_filtert;

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
  bool throw_assertion_error,
  optionalt<ci_lazy_methods_neededt> needed_lazy_methods,
  java_string_library_preprocesst &string_preprocess,
  const class_hierarchyt &class_hierarchy,
  bool threading_support,
  const optionalt<prefix_filtert> &method_context,
  bool assert_no_exceptions_thrown);

void create_method_stub_symbol(
  const irep_idt &identifier,
  const irep_idt &base_name,
  const irep_idt &pretty_name,
  const typet &type,
  const irep_idt &declaring_class,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler);

void java_bytecode_convert_method_lazy(
  symbolt &class_symbol,
  const irep_idt &method_identifier,
  const java_bytecode_parse_treet::methodt &,
  symbol_tablet &symbol_table,
  message_handlert &);

/// Extracts the names of parameters from the local variable table, creates
/// the parameter symbols and adds them to the symbol table.
/// \param m: the parsed method
/// \param method_identifier: the identifier of the method
/// \param parameters: the method's parameters
/// \param slots_for_parameters: the number of parameter slots available,
/// i.e. an integer
/// \param variables: a table of local variables
/// \param symbol_table: the symbol table
void create_parameter_symbols(
  const java_bytecode_parse_treet::methodt &m,
  const irep_idt &method_identifier,
  java_method_typet::parameterst &parameters,
  const java_bytecode_convert_methodt::method_offsett &slots_for_parameters,
  expanding_vectort<std::vector<java_bytecode_convert_methodt::variablet>>
    &variables,
  symbol_table_baset &symbol_table);

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_METHOD_H
