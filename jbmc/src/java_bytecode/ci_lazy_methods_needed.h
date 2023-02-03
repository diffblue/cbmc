/*******************************************************************\

Module: Context-insensitive lazy methods container

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Context-insensitive lazy methods container

#ifndef CPROVER_JAVA_BYTECODE_CI_LAZY_METHODS_H
#define CPROVER_JAVA_BYTECODE_CI_LAZY_METHODS_H

#include <unordered_set>

#include <util/irep.h>

class namespacet;
class pointer_typet;
class select_pointer_typet;
class symbol_table_baset;
class typet;

class ci_lazy_methods_neededt
{
public:
  ci_lazy_methods_neededt(
    std::unordered_set<irep_idt> &_callable_methods,
    std::unordered_set<irep_idt> &_instantiated_classes,
    const symbol_table_baset &_symbol_table,
    const select_pointer_typet &pointer_type_selector)
    : callable_methods(_callable_methods),
      instantiated_classes(_instantiated_classes),
      symbol_table(_symbol_table),
      pointer_type_selector(pointer_type_selector)
  {}

  void add_needed_method(const irep_idt &);
  // Returns true if new
  bool add_needed_class(const irep_idt &);

  void add_all_needed_classes(const pointer_typet &pointer_type);

private:
  // callable_methods is a vector because it's used as a work-list
  // which is periodically cleared. It can't be relied upon to
  // contain all methods that have previously been elaborated.
  // It should be changed to a set if we develop the need to use
  // it that way.
  std::unordered_set<irep_idt> &callable_methods;
  // instantiated_classes on the other hand is a true set of every class
  // found so far, so we can use a membership test to avoid
  // repeatedly exploring a class hierarchy.
  std::unordered_set<irep_idt> &instantiated_classes;
  const symbol_table_baset &symbol_table;

  const select_pointer_typet &pointer_type_selector;

  void add_clinit_call(const irep_idt &class_id);
  void add_cprover_nondet_initialize_if_it_exists(const irep_idt &class_id);

  void initialize_instantiated_classes_from_pointer(
    const pointer_typet &pointer_type,
    const namespacet &ns);

  void gather_field_types(const typet &class_type, const namespacet &ns);
};

#endif
