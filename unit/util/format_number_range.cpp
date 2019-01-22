/*******************************************************************\

Module: format_number_range unit tests

Author: Michael Tautschnig

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/format_number_range.h>

TEST_CASE(
  "Format a range of unsigned numbers",
  "[core][util][format_number_range]")
{
  const std::vector<unsigned> singleton = {1u};
  REQUIRE(format_number_range(singleton) == "1");

  const std::vector<unsigned> r1 = {0u, 42u};
  REQUIRE(format_number_range(r1) == "0,42");

  const std::vector<unsigned> r2 = {0u, 1u};
  REQUIRE(format_number_range(r2) == "0,1");

  const std::vector<unsigned> r3 = {1u, 2u, 3u};
  REQUIRE(format_number_range(r3) == "1-3");

  const std::vector<unsigned> r4 = {1u, 3u, 4u, 5u};
  REQUIRE(format_number_range(r4) == "1,3-5");

  const std::vector<unsigned> r5 = {1u, 10u, 11u, 12u, 42u};
  REQUIRE(format_number_range(r5) == "1,10-12,42");

  const std::vector<unsigned> r6 = {1u, 10u, 11u, 12u, 42u, 43u, 44u};
  REQUIRE(format_number_range(r6) == "1,10-12,42-44");
}
