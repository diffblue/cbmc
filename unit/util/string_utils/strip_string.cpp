/*******************************************************************\

Module: Unit tests of strip_string

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// strip_string Unit Tests

#include <testing-utils/catch.hpp>
#include <util/string_utils.h>

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
