/*******************************************************************\

Module: Java lambda code synthesis

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Java lambda code synthesis

#ifndef CPROVER_JAVA_BYTECODE_LAMBDA_SYNTHESIS_H
#define CPROVER_JAVA_BYTECODE_LAMBDA_SYNTHESIS_H

#include <java_bytecode/java_bytecode_parse_tree.h>
#include <java_bytecode/synthetic_methods_map.h>

#include <util/message.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>

irep_idt lambda_synthetic_class_name(
  const irep_idt &method_identifier,
  std::size_t instruction_address);

void create_invokedynamic_synthetic_classes(
  const irep_idt &method_identifier,
  const java_bytecode_parse_treet::methodt::instructionst &instructions,
  symbol_tablet &symbol_table,
  synthetic_methods_mapt &synthetic_methods,
  message_handlert &message_handler);

codet get_invokedynamic_synthetic_constructor(
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler);

codet get_invokedynamic_synthetic_method(
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler);

#endif // CPROVER_JAVA_BYTECODE_LAMBDA_SYNTHESIS_H
