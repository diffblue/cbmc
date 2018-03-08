/*******************************************************************\

Module: Context-insensitive lazy methods container

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Context-insensitive lazy methods container

#ifndef CPROVER_JAVA_BYTECODE_CI_LAZY_METHODS_H
#define CPROVER_JAVA_BYTECODE_CI_LAZY_METHODS_H

#include <vector>
#include <set>
#include <util/symbol_table.h>

class ci_lazy_methods_neededt
{
public:
  ci_lazy_methods_neededt(
    std::vector<irep_idt> &_callable_methods,
    std::set<irep_idt> &_instantiated_classes,
    symbol_tablet &_symbol_table):
  callable_methods(_callable_methods),
  instantiated_classes(_instantiated_classes),
  symbol_table(_symbol_table)
  {}

  void add_needed_method(const irep_idt &);
  // Returns true if new
  bool add_needed_class(const irep_idt &);

private:
  // callable_methods is a vector because it's used as a work-list
  // which is periodically cleared. It can't be relied upon to
  // contain all methods that have previously been elaborated.
  // It should be changed to a set if we develop the need to use
  // it that way.
  std::vector<irep_idt> &callable_methods;
  // instantiated_classes on the other hand is a true set of every class
  // found so far, so we can use a membership test to avoid
  // repeatedly exploring a class hierarchy.
  std::set<irep_idt> &instantiated_classes;
  symbol_tablet &symbol_table;
};

#endif
