/*******************************************************************\

Module: Unit test utilities

Author: Diffblue Limited.

\*******************************************************************/

#ifndef CPROVER_TESTING_UTILS_REQUIRE_SYMBOL_H
#define CPROVER_TESTING_UTILS_REQUIRE_SYMBOL_H

#include <util/symbol.h>
#include <util/symbol_table.h>

/// \file
/// Helper functions for getting symbols from the symbol table during unit tests

// NOLINTNEXTLINE(readability/namespace)
namespace require_symbol
{
const symbolt &require_symbol_exists(
  const symbol_tablet &symbol_table,
  const irep_idt &symbol_identifier);
}

#endif // CPROVER_TESTING_UTILS_REQUIRE_SYMBOL_H
