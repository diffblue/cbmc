/******************************************************************\

Module: parse_options unit tests

Author: Diffblue Ltd.

\******************************************************************/

#include <testing-utils/use_catch.h>
#include <util/parse_options.h>

TEST_CASE("align_center_with_border", "[core][util]")
{
  REQUIRE(
    align_center_with_border("test-text") ==
    "* *                        test-text                        * *");
}

TEST_CASE("help_entry", "[core][util]")
{
  REQUIRE(help_entry("--abc", "xyz", 8, 12) == " --abc  xyz\n");
  REQUIRE(help_entry("--abc", "xxxx x", 8, 12) == " --abc  xxxx\n        x\n");
  REQUIRE(help_entry("--abc", "xx xx", 8, 12) == " --abc  xx\n        xx\n");
  REQUIRE(help_entry("--abcdef", "xyz", 8, 12) == " --abcdef\n        xyz\n");
  REQUIRE(help_entry("--abcdefg", "xyz", 8, 12) == " --abcdefg\n        xyz\n");
}
