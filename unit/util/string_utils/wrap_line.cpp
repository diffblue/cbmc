/// Author: Daniel Poetzl

/// \file Tests for wrap_line()

#include <testing-utils/use_catch.h>
#include <util/string_utils.h>

TEST_CASE("Wrap line", "[core][util]")
{
  SECTION("Wrap without margin")
  {
    REQUIRE(wrap_line("x", 0, 1) == "x");
    REQUIRE(wrap_line("x x", 0, 1) == "x\nx");
    REQUIRE(wrap_line("x x x", 0, 1) == "x\nx\nx");

    REQUIRE(wrap_line("x x", 0, 2) == "x\nx");
    REQUIRE(wrap_line("xx xx xx", 0, 4) == "xx\nxx\nxx");

    REQUIRE(wrap_line("xx", 0, 1) == "xx");
  }

  SECTION("Wrap with margin")
  {
    REQUIRE(wrap_line("x", 1, 2) == " x");
    REQUIRE(wrap_line("x x", 1, 2) == " x\n x");
    REQUIRE(wrap_line("x x x", 1, 2) == " x\n x\n x");

    REQUIRE(wrap_line("x", 2, 3) == "  x");

    REQUIRE(wrap_line("xx", 1, 2) == "xx");
  }
}
