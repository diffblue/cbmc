/*******************************************************************\

Module: Smoke test for empty_namespacet

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Verify that the empty_namespace global is a usable
/// const namespacet & whose symbol table is empty. The test exists to
/// document the contract and to act as a regression test if anyone ever
/// changes the inheritance order or the base-from-member cast in
/// empty_namespacet's constructor.

#include <testing-utils/empty_namespace.h>
#include <testing-utils/use_catch.h>

TEST_CASE(
  "empty_namespace is a usable empty namespacet",
  "[core][testing-utils]")
{
  const namespacet &ns = empty_namespace;

  const symbolt *symbol = nullptr;
  REQUIRE(ns.lookup("does_not_exist", symbol));
  REQUIRE(symbol == nullptr);

  REQUIRE(ns.smallest_unused_suffix("x") == 0);
}
