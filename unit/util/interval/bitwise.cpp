/*******************************************************************\
 Module: Unit tests for variable/sensitivity/abstract_object::merge
 Author: DiffBlue Limited
\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/interval.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

SCENARIO("bitwise interval domain", "[core][analyses][interval][bitwise]")
{
  WHEN("We have two unsigned single value intervals - 5 and 9")
  {
    const unsignedbv_typet &unsigned_int = unsignedbv_typet(32);
    constant_interval_exprt five =
      constant_interval_exprt(from_integer(5, unsigned_int));
    constant_interval_exprt nine =
      constant_interval_exprt(from_integer(9, unsigned_int));

    THEN("Bitwise or should yield bitwise representation of 13")
    {
      REQUIRE(
        five.bitwise_or(nine) ==
        constant_interval_exprt(from_integer(13, unsigned_int)));
    }

    THEN("Bitwise and should yield bitwise representation of 1")
    {
      REQUIRE(
        five.bitwise_and(nine) ==
        constant_interval_exprt(from_integer(1, unsigned_int)));
      REQUIRE(
        (five & nine) ==
        constant_interval_exprt(from_integer(1, unsigned_int)));
    }

    THEN("Bitwise xor should yield bitwise representation of 12")
    {
      REQUIRE(
        five.bitwise_xor(nine) ==
        constant_interval_exprt(from_integer(12, unsigned_int)));
    }

    THEN("Left shift on the 5 should produce 10")
    {
      REQUIRE(
        five.left_shift(
          constant_interval_exprt(from_integer(1, unsigned_int))) ==
        constant_interval_exprt(from_integer(10, unsigned_int)));
    }

    THEN("Right shift on the 5 should produce 2")
    {
      REQUIRE(
        five.right_shift(
          constant_interval_exprt(from_integer(1, unsigned_int))) ==
        constant_interval_exprt(from_integer(2, unsigned_int)));
    }
  }
}
