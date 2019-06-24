/*******************************************************************\

Module: format_number_range unit tests

Author: Michael Tautschnig

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/exception_utils.h>
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

TEST_CASE(
  "Parse a range of unsigned numbers",
  "[core][util][format_number_range]")
{
  const std::vector<unsigned> singleton = {1u};
  REQUIRE(parse_number_range("1") == singleton);

  const std::vector<unsigned> r1 = {0u, 42u};
  REQUIRE(parse_number_range("0,42") == r1);

  const std::vector<unsigned> r2 = {0u, 1u};
  REQUIRE(parse_number_range("0,1") == r2);

  const std::vector<unsigned> r3 = {1u, 2u, 3u};
  REQUIRE(parse_number_range("1-3") == r3);

  const std::vector<unsigned> r4 = {1u, 3u, 4u, 5u};
  REQUIRE(parse_number_range("1,3-5") == r4);

  const std::vector<unsigned> r5 = {1u, 10u, 11u, 12u, 42u};
  REQUIRE(parse_number_range("1,10-12,42") == r5);

  const std::vector<unsigned> r6 = {1u, 10u, 11u, 12u, 42u, 43u, 44u};
  REQUIRE(parse_number_range("1,10-12,42-44") == r6);

  REQUIRE_THROWS_AS(parse_number_range(""), deserialization_exceptiont);
  REQUIRE_THROWS_AS(parse_number_range(","), deserialization_exceptiont);
  REQUIRE_THROWS_AS(parse_number_range("1,"), deserialization_exceptiont);
  REQUIRE_THROWS_AS(parse_number_range("-5"), deserialization_exceptiont);
  REQUIRE_THROWS_AS(parse_number_range("0,1-"), deserialization_exceptiont);
  REQUIRE_THROWS_AS(parse_number_range("1, 2"), deserialization_exceptiont);
  REQUIRE_THROWS_AS(parse_number_range("4-2"), deserialization_exceptiont);
}
