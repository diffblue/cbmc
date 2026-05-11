/*******************************************************************\

Module: Unit tests of trim_from_last_delimiter

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// trim_from_last_delimiter Unit Tests

#include <util/string_utils.h>

#include <testing-utils/use_catch.h>

#include <string_view>

TEST_CASE(
  "trim_from_last_delimiter",
  "[core][utils][string_utils][trim_from_last_delimiter]")
{
  REQUIRE(trim_from_last_delimiter("a.b.c", '.') == "a.b");
  REQUIRE(trim_from_last_delimiter("abc", '.') == "");
  REQUIRE(trim_from_last_delimiter("", '.') == "");
}

TEST_CASE(
  "trim_from_last_delimiter honours string_view length over a "
  "non-NUL-terminated buffer",
  "[core][utils][string_utils][trim_from_last_delimiter]")
{
  // Without a trailing NUL: a regression where the implementation
  // walked the buffer until '\0' would read past the end.
  const char buf[] = {'a', '.', 'b', '.', 'c', 'X', 'Y'};
  std::string_view sv{buf, 5};
  REQUIRE(trim_from_last_delimiter(sv, '.') == "a.b");
}
