/*******************************************************************\

Module: Java Static Initializers

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_STATIC_INITIALIZERS_H
#define CPROVER_JAVA_BYTECODE_JAVA_STATIC_INITIALIZERS_H

#include <unordered_set>

#include <util/symbol_table.h>
#include <util/std_code.h>
#include <java_bytecode/object_factory_parameters.h>
#include <java_bytecode/select_pointer_type.h>
#include <java_bytecode/synthetic_methods_map.h>

irep_idt clinit_wrapper_name(const irep_idt &class_name);

bool is_clinit_wrapper_function(const irep_idt &function_id);

void create_static_initializer_wrappers(
  symbol_tablet &symbol_table,
  synthetic_methods_mapt &synthetic_methods);

codet get_clinit_wrapper_body(
  const irep_idt &function_id, const symbol_table_baset &symbol_table);

class stub_global_initializer_factoryt
{
  /// Maps class symbols onto the stub globals that belong to them
  typedef std::unordered_multimap<irep_idt, irep_idt, irep_id_hash>
    stub_globals_by_classt;
  stub_globals_by_classt stub_globals_by_class;

public:
  void create_stub_global_initializer_symbols(
    symbol_tablet &symbol_table,
    const std::unordered_set<irep_idt, irep_id_hash> &stub_globals_set,
    synthetic_methods_mapt &synthetic_methods);

  codet get_stub_initializer_body(
    const irep_idt &function_id,
    symbol_table_baset &symbol_table,
    const object_factory_parameterst &object_factory_parameters,
    const select_pointer_typet &pointer_type_selector);
};

void create_stub_global_initializers(
  symbol_tablet &symbol_table,
  const std::unordered_set<irep_idt, irep_id_hash> &stub_globals_set,
  const object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector);

#endif
