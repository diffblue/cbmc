/*******************************************************************\

Module: Java Bytecode

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Collect methods needed to be loaded using the lazy method

#ifndef CPROVER_JAVA_BYTECODE_GATHER_METHODS_LAZILY_H
#define CPROVER_JAVA_BYTECODE_GATHER_METHODS_LAZILY_H

#include "java_bytecode_parse_tree.h"
#include "synthetic_methods_map.h"

#include <functional>
#include <map>
#include <unordered_set>

#include <util/irep.h>

#include <goto-programs/class_hierarchy.h>

class ci_lazy_methods_neededt;
class java_class_loadert;
class message_handlert;
class select_pointer_typet;
class symbol_table_baset;

// Map from method id to class_method_and_bytecodet
class method_bytecodet
{
public:
  /// Pair of class id and methodt
  struct class_method_and_bytecodet
  {
    irep_idt class_id;
    irep_idt method_id;
    const java_bytecode_parse_treet::methodt &method;
  };

  typedef optionalt<std::reference_wrapper<const class_method_and_bytecodet>>
    opt_reft;

private:
  typedef std::map<irep_idt, class_method_and_bytecodet> mapt;
  mapt map;

public:
  bool contains_method(const irep_idt &method_id) const
  {
    return map.count(method_id) != 0;
  }

  void add(const class_method_and_bytecodet &method_class_and_bytecode)
  {
    map.emplace(
      std::make_pair(
        method_class_and_bytecode.method_id, method_class_and_bytecode));
  }

  void add(
    const irep_idt &class_id,
    const irep_idt &method_id,
    const java_bytecode_parse_treet::methodt &method)
  {
    add(class_method_and_bytecodet{class_id, method_id, method});
  }

  mapt::const_iterator begin() const
  {
    return map.begin();
  }
  mapt::const_iterator end() const
  {
    return map.end();
  }

  opt_reft get(const irep_idt &method_id)
  {
    const auto it = map.find(method_id);
    if(it == map.end())
      return std::nullopt;
    return std::cref(it->second);
  }
};

typedef std::function<
  bool(const irep_idt &function_id, ci_lazy_methods_neededt)>
  method_convertert;

typedef std::function<std::vector<irep_idt>(const symbol_table_baset &)>
  load_extra_methodst;

class ci_lazy_methodst
{
public:
  ci_lazy_methodst(
    const symbol_table_baset &symbol_table,
    const irep_idt &main_class,
    const std::vector<irep_idt> &main_jar_classes,
    const std::vector<load_extra_methodst> &lazy_methods_extra_entry_points,
    java_class_loadert &java_class_loader,
    const std::vector<irep_idt> &extra_instantiated_classes,
    const select_pointer_typet &pointer_type_selector,
    const synthetic_methods_mapt &synthetic_methods);

  // not const since messaget
  bool operator()(
    symbol_table_baset &symbol_table,
    method_bytecodet &method_bytecode,
    const method_convertert &method_converter,
    message_handlert &message_handler);

private:
  void initialize_instantiated_classes(
    const std::unordered_set<irep_idt> &entry_points,
    const namespacet &ns,
    ci_lazy_methods_neededt &needed_lazy_methods);

  void gather_virtual_callsites(
    const exprt &e,
    std::unordered_set<class_method_descriptor_exprt, irep_hash> &result);

  void get_virtual_method_targets(
    const class_method_descriptor_exprt &called_function,
    const std::unordered_set<irep_idt> &instantiated_classes,
    std::unordered_set<irep_idt> &callable_methods,
    symbol_table_baset &symbol_table);

  void gather_needed_globals(
    const exprt &e,
    const symbol_table_baset &symbol_table,
    symbol_table_baset &needed);

  irep_idt get_virtual_method_target(
    const std::unordered_set<irep_idt> &instantiated_classes,
    const irep_idt &call_basename,
    const irep_idt &classname,
    const symbol_table_baset &symbol_table);

  static irep_idt build_virtual_method_name(
    const irep_idt &class_name,
    const irep_idt &component_method_name);

  class_hierarchyt class_hierarchy;
  irep_idt main_class;
  std::vector<irep_idt> main_jar_classes;
  const std::vector<load_extra_methodst> &lazy_methods_extra_entry_points;
  java_class_loadert &java_class_loader;
  const std::vector<irep_idt> &extra_instantiated_classes;
  const select_pointer_typet &pointer_type_selector;
  const synthetic_methods_mapt &synthetic_methods;

  std::unordered_set<irep_idt> entry_point_methods(
    const symbol_table_baset &symbol_table,
    message_handlert &message_handler);

  struct convert_method_resultt
  {
    bool class_initializer_seen = false;
    bool new_method_seen = false;
  };

  convert_method_resultt convert_and_analyze_method(
    const method_convertert &method_converter,
    std::unordered_set<irep_idt> &methods_already_populated,
    const bool class_initializer_already_seen,
    const irep_idt &method_name,
    symbol_table_baset &symbol_table,
    std::unordered_set<irep_idt> &methods_to_convert_later,
    std::unordered_set<irep_idt> &instantiated_classes,
    std::unordered_set<class_method_descriptor_exprt, irep_hash>
      &called_virtual_functions,
    message_handlert &message_handler);

  bool handle_virtual_methods_with_no_callees(
    std::unordered_set<irep_idt> &methods_to_convert_later,
    std::unordered_set<irep_idt> &instantiated_classes,
    const std::unordered_set<class_method_descriptor_exprt, irep_hash>
      &virtual_functions,
    symbol_table_baset &symbol_table);
};

#endif // CPROVER_JAVA_BYTECODE_GATHER_METHODS_LAZILY_H
