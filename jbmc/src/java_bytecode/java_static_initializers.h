/*******************************************************************\

Module: Java Static Initializers

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_STATIC_INITIALIZERS_H
#define CPROVER_JAVA_BYTECODE_JAVA_STATIC_INITIALIZERS_H

#include "assignments_from_json.h"
#include "ci_lazy_methods_needed.h"
#include "java_object_factory_parameters.h"
#include "select_pointer_type.h"
#include "synthetic_methods_map.h"

#include <unordered_set>

#include <util/message.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

irep_idt clinit_wrapper_name(const irep_idt &class_name);
irep_idt user_specified_clinit_name(const irep_idt &class_name);

bool is_clinit_wrapper_function(const irep_idt &function_id);
bool is_clinit_function(const irep_idt &function_id);
bool is_user_specified_clinit_function(const irep_idt &function_id);

void create_static_initializer_symbols(
  symbol_tablet &symbol_table,
  synthetic_methods_mapt &synthetic_methods,
  const bool thread_safe,
  const bool is_user_clinit_needed);

code_blockt get_thread_safe_clinit_wrapper_body(
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  const bool nondet_static,
  const bool replace_clinit,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  message_handlert &message_handler);

code_ifthenelset get_clinit_wrapper_body(
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  const bool nondet_static,
  const bool replace_clinit,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  message_handlert &message_handler);

/// \return map associating classes to the symbols they declare
std::unordered_multimap<irep_idt, symbolt>
class_to_declared_symbols(const symbol_tablet &symbol_table);

/// Create the body of a user_specified_clinit function for a given class, which
/// includes assignments for all static fields of the class to values read from
/// an input file. If the file could not be parsed or an entry for this class
/// could not be found in it, the user_specified_clinit function will only
/// contain a call to the "real" clinit function, and not include any
/// assignments itself. If an entry for this class is found but some of its
/// static fields are not mentioned in the input file, those fields will be
/// assigned default values (zero or null).
/// \param class_id: the id of the class to create a user_specified_clinit
///   function body for.
/// \param static_values_json: JSON object containing values of static fields.
///   The format is expected to be a map whose keys are class names, and whose
///   values are maps from static field names to values.
/// \param symbol_table: used to look up and create new symbols
/// \param needed_lazy_methods: used to mark any runtime types given in the
///   input file as needed
/// \param max_user_array_length: maximum value for constant or variable length
///   arrays. Any arrays that were specified to be of nondeterministic length in
///   the input file will be limited by this value.
/// \param references: map to keep track of reference-equal objets.
/// \param class_to_declared_symbols_map: map classes to the symbols that
///   they declare.
/// \return the body of the user_specified_clinit function as a code block.
code_blockt get_user_specified_clinit_body(
  const irep_idt &class_id,
  const json_objectt &static_values_json,
  symbol_table_baset &symbol_table,
  optionalt<ci_lazy_methods_neededt> needed_lazy_methods,
  size_t max_user_array_length,
  std::unordered_map<std::string, object_creation_referencet> &references,
  const std::unordered_multimap<irep_idt, symbolt>
    &class_to_declared_symbols_map);

class stub_global_initializer_factoryt
{
  /// Maps class symbols onto the stub globals that belong to them
  typedef std::unordered_multimap<irep_idt, irep_idt> stub_globals_by_classt;
  stub_globals_by_classt stub_globals_by_class;

public:
  void create_stub_global_initializer_symbols(
    symbol_tablet &symbol_table,
    const std::unordered_set<irep_idt> &stub_globals_set,
    synthetic_methods_mapt &synthetic_methods);

  code_blockt get_stub_initializer_body(
    const irep_idt &function_id,
    symbol_table_baset &symbol_table,
    const java_object_factory_parameterst &object_factory_parameters,
    const select_pointer_typet &pointer_type_selector,
    message_handlert &message_handler);
};

void create_stub_global_initializers(
  symbol_tablet &symbol_table,
  const std::unordered_set<irep_idt> &stub_globals_set,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector);

#endif
