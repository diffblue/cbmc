/*******************************************************************\

Module: Unit tests for memory_info.h

Author: Michael Tautschnig

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/memory_info.h>

#include <sstream>

TEST_CASE("memory_info returns some output", "[core][util][memory_info]")
{
  std::ostringstream oss;
  memory_info(oss);

  REQUIRE(!oss.str().empty());
}
