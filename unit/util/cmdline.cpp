/*******************************************************************\

Module: cmdlinet unit tests

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <util/cmdline.h>

TEST_CASE("cmdlinet::has_option", "[core][util][cmdline]")
{
  cmdlinet cmdline;
  REQUIRE(!cmdline.parse(0, nullptr, "(a)(b):"));
  REQUIRE(cmdline.has_option("a"));
  REQUIRE(cmdline.has_option("b"));
  REQUIRE(!cmdline.has_option("c"));
}
