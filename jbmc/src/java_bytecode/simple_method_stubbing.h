/*******************************************************************\

Module: Simple Java method stubbing

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Java simple opaque stub generation

#ifndef CPROVER_JAVA_BYTECODE_SIMPLE_METHOD_STUBBING_H
#define CPROVER_JAVA_BYTECODE_SIMPLE_METHOD_STUBBING_H

#include <util/irep.h>

class message_handlert;
struct java_object_factory_parameterst;
class symbol_table_baset;

void java_generate_simple_method_stub(
  const irep_idt &function_name,
  symbol_table_baset &symbol_table,
  bool assume_non_null,
  const java_object_factory_parameterst &object_factory_parameters,
  message_handlert &message_handler);

void java_generate_simple_method_stubs(
  symbol_table_baset &symbol_table,
  bool assume_non_null,
  const java_object_factory_parameterst &object_factory_parameters,
  message_handlert &message_handler);

#endif
