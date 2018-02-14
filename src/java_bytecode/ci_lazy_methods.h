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
#include <java_bytecode/ci_lazy_methods_needed.h>
#include <java_bytecode/select_pointer_type.h>
#include <java_bytecode/synthetic_methods_map.h>

class java_string_library_preprocesst;

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
      return opt_reft();
    return std::cref(it->second);
  }
};

typedef std::function<
  bool(const irep_idt &function_id, ci_lazy_methods_neededt)>
  method_convertert;

class ci_lazy_methodst:public messaget
{
public:
  ci_lazy_methodst(
    const symbol_tablet &symbol_table,
    const irep_idt &main_class,
    const std::vector<irep_idt> &main_jar_classes,
    const std::vector<irep_idt> &lazy_methods_extra_entry_points,
    java_class_loadert &java_class_loader,
    const std::vector<irep_idt> &extra_needed_classes,
    const select_pointer_typet &pointer_type_selector,
    message_handlert &message_handler,
    const synthetic_methods_mapt &synthetic_methods);

  // not const since messaget
  bool operator()(
    symbol_tablet &symbol_table,
    method_bytecodet &method_bytecode,
    const method_convertert &method_converter);

private:
  void resolve_method_names(
    std::vector<irep_idt> &methods,
    const symbol_tablet &symbol_table);

  void initialize_needed_classes(
    const std::vector<irep_idt> &entry_points,
    const namespacet &ns,
    ci_lazy_methods_neededt &needed_lazy_methods);

  void initialize_all_needed_classes_from_pointer(
    const pointer_typet &pointer_type,
    const namespacet &ns,
    ci_lazy_methods_neededt &needed_lazy_methods);

  void initialize_needed_classes_from_pointer(
    const pointer_typet &pointer_type,
    const namespacet &ns,
    ci_lazy_methods_neededt &needed_lazy_methods);

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

  void gather_field_types(
    const typet &class_type,
    const namespacet &ns,
    ci_lazy_methods_neededt &needed_lazy_methods);

  irep_idt get_virtual_method_target(
    const std::set<irep_idt> &needed_classes,
    const irep_idt &call_basename,
    const irep_idt &classname,
    const symbol_tablet &symbol_table);

  static irep_idt build_virtual_method_name(
    const irep_idt &class_name,
    const irep_idt &component_method_name);

  class_hierarchyt class_hierarchy;
  irep_idt main_class;
  std::vector<irep_idt> main_jar_classes;
  std::vector<irep_idt> lazy_methods_extra_entry_points;
  java_class_loadert &java_class_loader;
  const std::vector<irep_idt> &extra_needed_classes;
  const select_pointer_typet &pointer_type_selector;
  const synthetic_methods_mapt &synthetic_methods;
};

#endif // CPROVER_JAVA_BYTECODE_GATHER_METHODS_LAZILY_H
