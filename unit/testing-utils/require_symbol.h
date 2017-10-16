/*******************************************************************\

 Module: Unit test utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Helper functions for requiring properties of symbols

#include <util/symbol.h>
#include <util/std_types.h>

#ifndef CPROVER_TESTING_UTILS_REQUIRE_SYMBOL_H
#define CPROVER_TESTING_UTILS_REQUIRE_SYMBOL_H

// NOLINTNEXTLINE(readability/namespace)
namespace require_symbol
{
  const class_typet &require_complete_class(
    const symbolt &class_symbol);
}

#endif // CPROVER_TESTING_UTILS_REQUIRE_SYMBOL_H
