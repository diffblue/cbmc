/*******************************************************************\

Module: Unit tests of strip_string

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// strip_string Unit Tests

#include <util/string_utils.h>

#include <testing-utils/use_catch.h>

#include <string_view>

SCENARIO("strip_string", "[core][utils][string_utils][strip_string]")
{
  GIVEN("A string with some whitespace in it")
  {
    std::string string = "   x y ";
    WHEN("Using strip_string")
    {
      std::string result = strip_string(string);
      THEN(
        "Whitespace at either end should be removed, but not internal "
        "whitespace")
      {
        REQUIRE(result == "x y");
      }
    }
  }
}

TEST_CASE(
  "strip_string honours string_view length over a non-NUL-terminated buffer",
  "[core][utils][string_utils][strip_string]")
{
  // Without a trailing NUL: a regression where the implementation
  // walked the buffer until '\0' would read past the end.
  const char buf[] = {' ', 'a', ' ', 'b', ' ', 'X', 'Y'};
  std::string_view sv{buf, 5};
  REQUIRE(strip_string(sv) == "a b");
}
