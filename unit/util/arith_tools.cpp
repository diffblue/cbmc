/*******************************************************************\

Module: Unit test for util/arith_tools.h

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>

#include <testing-utils/use_catch.h>

TEST_CASE("is_power_of_two", "[unit][util][arith_tools]")
{
  REQUIRE(!is_power_of_two(0));
  REQUIRE(is_power_of_two(1));
  REQUIRE(is_power_of_two(2));
  REQUIRE(!is_power_of_two(3));
  REQUIRE(is_power_of_two(4));
}
