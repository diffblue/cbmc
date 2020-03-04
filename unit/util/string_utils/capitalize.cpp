/*******************************************************************\

Module: Unit tests for string utilities

Author: Thomas Kiley

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <util/string_utils.h>

TEST_CASE("capitalize", "[core][util][string_utils]")
{
  REQUIRE(capitalize("") == "");
  REQUIRE(capitalize("abc") == "Abc");
  REQUIRE(capitalize("aBc") == "ABc");
  REQUIRE(capitalize("ABc") == "ABc");
  REQUIRE(capitalize("abc def") == "Abc def");
  REQUIRE(capitalize("1") == "1");
}
