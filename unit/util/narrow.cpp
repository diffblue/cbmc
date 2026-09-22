/*******************************************************************\
Module: Unit tests for narrow.h
Author: Michael Tautschnig
\*******************************************************************/

/// \file
/// Unit tests for the narrowing conversions in util/narrow.h

#include <util/narrow.h>

#include <testing-utils/use_catch.h>

#include <stdexcept>

TEST_CASE("narrow_cast truncates like static_cast", "[core][util][narrow]")
{
  REQUIRE(narrow_cast<signed char>(300L) == static_cast<signed char>(300L));
  REQUIRE(narrow_cast<unsigned char>(-1) == 255);
}

TEST_CASE("narrow keeps representable values", "[core][util][narrow]")
{
  REQUIRE(narrow<signed char>(127L) == 127);
  REQUIRE(narrow<signed char>(-128L) == -128);
  REQUIRE(narrow<unsigned>(0x7fffffffL) == 0x7fffffffu);
}

TEST_CASE(
  "narrow_or_throw_out_of_range throws for exactly the values that do not fit",
  "[core][util][narrow]")
{
  REQUIRE(narrow_or_throw_out_of_range<signed char>(127L) == 127);
  REQUIRE(narrow_or_throw_out_of_range<signed char>(-128L) == -128);
  REQUIRE_THROWS_AS(
    narrow_or_throw_out_of_range<signed char>(128L), std::out_of_range);
  REQUIRE_THROWS_AS(
    narrow_or_throw_out_of_range<signed char>(-129L), std::out_of_range);
  REQUIRE_THROWS_AS(
    narrow_or_throw_out_of_range<unsigned>(-1L), std::out_of_range);
  REQUIRE(narrow_or_throw_out_of_range<int>(-1L) == -1);
}
