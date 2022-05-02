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
  const std::vector<mp_integer> singleton = {1};
  REQUIRE(format_number_range(singleton) == "1");

  const std::vector<mp_integer> r1 = {0, 42};
  REQUIRE(format_number_range(r1) == "0,42");

  const std::vector<mp_integer> r2 = {0, 1};
  REQUIRE(format_number_range(r2) == "0,1");

  const std::vector<mp_integer> r3 = {1, 2, 3};
  REQUIRE(format_number_range(r3) == "1-3");

  const std::vector<mp_integer> r4 = {1, 3, 4, 5};
  REQUIRE(format_number_range(r4) == "1,3-5");

  const std::vector<mp_integer> r5 = {1, 10, 11, 12, 42};
  REQUIRE(format_number_range(r5) == "1,10-12,42");

  const std::vector<mp_integer> r6 = {1, 10, 11, 12, 42, 43, 44};
  REQUIRE(format_number_range(r6) == "1,10-12,42-44");
}

TEST_CASE(
  "Parse a range of unsigned numbers",
  "[core][util][format_number_range]")
{
  const std::vector<mp_integer> singleton = {1};
  REQUIRE(parse_number_range("1") == singleton);

  const std::vector<mp_integer> r1 = {0, 42};
  REQUIRE(parse_number_range("0,42") == r1);

  const std::vector<mp_integer> r2 = {0, 1};
  REQUIRE(parse_number_range("0,1") == r2);

  const std::vector<mp_integer> r3 = {1, 2, 3};
  REQUIRE(parse_number_range("1-3") == r3);

  const std::vector<mp_integer> r4 = {1, 3, 4, 5};
  REQUIRE(parse_number_range("1,3-5") == r4);

  const std::vector<mp_integer> r5 = {1, 10, 11, 12, 42};
  REQUIRE(parse_number_range("1,10-12,42") == r5);

  const std::vector<mp_integer> r6 = {1, 10, 11, 12, 42, 43, 44};
  REQUIRE(parse_number_range("1,10-12,42-44") == r6);

  REQUIRE_THROWS_AS(parse_number_range(""), deserialization_exceptiont);
  REQUIRE_THROWS_AS(parse_number_range(","), deserialization_exceptiont);
  REQUIRE_THROWS_AS(parse_number_range("1,"), deserialization_exceptiont);
  REQUIRE_THROWS_AS(parse_number_range("-5"), deserialization_exceptiont);
  REQUIRE_THROWS_AS(parse_number_range("0,1-"), deserialization_exceptiont);
  REQUIRE_THROWS_AS(parse_number_range("1, 2"), deserialization_exceptiont);
  REQUIRE_THROWS_AS(parse_number_range("4-2"), deserialization_exceptiont);
}
