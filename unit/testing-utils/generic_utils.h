/*******************************************************************\

 Module: Unit test utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Utility methods for dealing with Java generics in unit tests

#ifndef CPROVER_TESTING_UTILS_GENERIC_UTILS_H
#define CPROVER_TESTING_UTILS_GENERIC_UTILS_H

#include <util/irep.h>
#include <util/symbol_table.h>

// NOLINTNEXTLINE(readability/namespace)
namespace generic_utils
{
void specialise_generic(
  const java_generic_typet &example_type,
  symbol_tablet &new_symbol_table);

void specialise_generic_from_component(
  const irep_idt &class_name,
  const irep_idt &component_name,
  symbol_tablet &new_symbol_table);
}

#endif // CPROVER_TESTING_UTILS_GENERIC_UTILS_H
