/*******************************************************************\

 Module: Java Bytecode

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Collect methods needed to be loaded using the lazy method

#ifndef CPROVER_JAVA_BYTECODE_GATHER_METHODS_LAZILY_H
#define CPROVER_JAVA_BYTECODE_GATHER_METHODS_LAZILY_H

#include <map>
#include <functional>

#include <util/irep.h>
#include <util/symbol_table.h>
#include <util/message.h>
#include <goto-programs/class_hierarchy.h>
#include <java_bytecode/java_bytecode_parse_tree.h>
#include <java_bytecode/java_class_loader.h>
#include <java_bytecode/ci_lazy_methods.h>

class java_string_library_preprocesst;

typedef std::pair<
          const symbolt *,
          const java_bytecode_parse_treet::methodt *>
  lazy_method_valuet;

typedef std::map<irep_idt, lazy_method_valuet>
  lazy_methodst;

class gather_methods_lazilyt:public messaget
{
public:
  gather_methods_lazilyt(
    const symbol_tablet &symbol_table,
    const irep_idt &main_class,
    const std::vector<irep_idt> &main_jar_classes,
    const std::vector<irep_idt> &lazy_methods_extra_entry_points,
    java_class_loadert &java_class_loader,
    message_handlert &message_handler);

  // not const since messaget
  bool operator()(
    symbol_tablet &symbol_table,
    lazy_methodst &lazy_methods,
    std::function<void(
      const symbolt &,
      const java_bytecode_parse_treet::methodt &,
      ci_lazy_methodst)> method_converter);

private:
  void resolve_method_names(
    std::vector<irep_idt> &methods,
    const symbol_tablet &symbol_table);

  void initialize_needed_classes(
    const std::vector<irep_idt> &entry_points,
    const namespacet &ns,
    ci_lazy_methodst &lazy_methods);

  void initialize_needed_classes_from_pointer(
    const pointer_typet &pointer_type,
    const namespacet &ns,
    ci_lazy_methodst &lazy_methods);

  void gather_virtual_callsites(
    const exprt &e,
    std::vector<const code_function_callt *> &result);

  void get_virtual_method_targets(
    const code_function_callt &c,
    const std::set<irep_idt> &needed_classes,
    std::vector<irep_idt> &needed_methods,
    symbol_tablet &symbol_table);

  void gather_needed_globals(
    const exprt &e,
    const symbol_tablet &symbol_table,
    symbol_tablet &needed);

  void gather_field_types(const typet &class_type,
    const namespacet &ns,
    ci_lazy_methodst &lazy_methods);

  irep_idt get_virtual_method_target(
    const std::set<irep_idt> &needed_classes,
    const irep_idt &call_basename,
    const irep_idt &classname,
    const symbol_tablet &symbol_table);

  class_hierarchyt class_hierarchy;
  const irep_idt main_class;
  const std::vector<irep_idt> main_jar_classes;
  const std::vector<irep_idt> lazy_methods_extra_entry_points;
  java_class_loadert &java_class_loader;
};

#endif // CPROVER_JAVA_BYTECODE_GATHER_METHODS_LAZILY_H
