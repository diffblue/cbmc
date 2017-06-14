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

class ci_lazy_methodst
{
public:
  ci_lazy_methodst(
    std::vector<irep_idt> &_needed_methods,
    std::set<irep_idt> &_needed_classes,
    symbol_tablet &_symbol_table):
  needed_methods(_needed_methods),
  needed_classes(_needed_classes),
  symbol_table(_symbol_table)
  {}

  void add_needed_method(const irep_idt &);
  // Returns true if new
  bool add_needed_class(const irep_idt &);

private:
  // needed_methods is a vector because it's used as a work-list
  // which is periodically cleared. It can't be relied upon to
  // contain all methods that have previously been elaborated.
  // It should be changed to a set if we develop the need to use
  // it that way.
  std::vector<irep_idt> &needed_methods;
  // needed_classes on the other hand is a true set of every class
  // found so far, so we can use a membership test to avoid
  // repeatedly exploring a class hierarchy.
  std::set<irep_idt> &needed_classes;
  symbol_tablet &symbol_table;
};

#endif
