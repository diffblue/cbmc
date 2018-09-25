/*******************************************************************\

Module: Unit test for std_expr.h/std_expr.cpp

Author: Diffblue Ltd

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/std_types.h>

TEST_CASE("for a division expression...")
{
  auto dividend = from_integer(10, integer_typet());
  auto divisor = from_integer(5, integer_typet());
  auto div = div_exprt(dividend, divisor);

  SECTION("its divisor and dividend have the values assigned to them")
  {
    REQUIRE(div.dividend() == dividend);
    REQUIRE(div.divisor() == divisor);
  }

  SECTION("its type is that of its operands")
  {
    REQUIRE(div.type() == integer_typet());
  }
}
