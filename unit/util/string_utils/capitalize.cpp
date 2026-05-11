/*******************************************************************\

Module: Unit tests for string utilities

Author: Thomas Kiley

\*******************************************************************/

#include <util/string_utils.h>

#include <testing-utils/use_catch.h>

#include <string_view>

TEST_CASE("capitalize", "[core][util][string_utils]")
{
  REQUIRE(capitalize("") == "");
  REQUIRE(capitalize("abc") == "Abc");
  REQUIRE(capitalize("aBc") == "ABc");
  REQUIRE(capitalize("ABc") == "ABc");
  REQUIRE(capitalize("abc def") == "Abc def");
  REQUIRE(capitalize("1") == "1");
}

TEST_CASE(
  "capitalize honours string_view length over a non-NUL-terminated buffer",
  "[core][util][string_utils]")
{
  // Without a trailing NUL: a regression where the implementation
  // walked the buffer until '\0' would read past the end.
  const char buf[] = {'a', 'b', 'c', 'X', 'Y'};
  std::string_view sv{buf, 3};
  REQUIRE(capitalize(sv) == "Abc");
}
