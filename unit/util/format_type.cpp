/*******************************************************************\

 Module: Unit tests for `format` function on types

 Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/format.h>
#include <util/format_type.h>
#include <util/std_expr.h>

#include <testing-utils/use_catch.h>

TEST_CASE("Format a range type", "[core][util][format_type]")
{
  auto type = range_typet(1, 10);
  REQUIRE(format_to_string(type) == "{ 1, ..., 10 }");
}
