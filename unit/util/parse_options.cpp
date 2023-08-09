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
