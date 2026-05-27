/*******************************************************************\

Module: Unit tests of escape

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// escape Unit Tests

#include <util/string_utils.h>

#include <testing-utils/use_catch.h>

#include <string_view>

TEST_CASE("escape", "[core][utils][string_utils][escape]")
{
  REQUIRE(escape("") == "");
  REQUIRE(escape("abc") == "abc");
  REQUIRE(escape("a\"b") == "a\\\"b");
  REQUIRE(escape("a\\b") == "a\\\\b");
  // characters other than `"` and `\` are passed through unchanged
  REQUIRE(escape("a'b") == "a'b");
}

TEST_CASE(
  "escape honours string_view length over a non-NUL-terminated buffer",
  "[core][utils][string_utils][escape]")
{
  // Without a trailing NUL: a regression where the implementation
  // walked the buffer until '\0' would read past the end.
  const char buf[] = {'a', '"', 'b', 'X', 'Y'};
  std::string_view sv{buf, 3};
  REQUIRE(escape(sv) == "a\\\"b");
}
