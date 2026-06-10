/*******************************************************************\

Module: Unit test utilities

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// An empty namespacet for unit tests that don't need symbols.

#ifndef CPROVER_TESTING_UTILS_EMPTY_NAMESPACE_H
#define CPROVER_TESTING_UTILS_EMPTY_NAMESPACE_H

#include <util/namespace.h>
#include <util/symbol_table.h>

/// A namespacet that contains an empty symbol table, for use in tests that
/// need a namespacet but don't actually look up any symbols.
/// This avoids the boilerplate of declaring a symbol_tablet and namespacet
/// in every test.
class empty_namespacet : private symbol_tablet, public namespacet
{
public:
  empty_namespacet() : namespacet{static_cast<symbol_tablet &>(*this)}
  {
  }

  empty_namespacet(const empty_namespacet &) = delete;
  empty_namespacet(empty_namespacet &&) = delete;
  empty_namespacet &operator=(const empty_namespacet &) = delete;
  empty_namespacet &operator=(empty_namespacet &&) = delete;
};

extern const empty_namespacet empty_namespace;

#endif // CPROVER_TESTING_UTILS_EMPTY_NAMESPACE_H
