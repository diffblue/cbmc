/*******************************************************************\
 Module: Unit tests for variable/sensitivity/abstract_object::merge
 Author: DiffBlue Limited
\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/interval.h>

SCENARIO("bitwise interval domain", "[core][analyses][interval][bitwise]")
{
  WHEN("We have two unsigned single value intervals - 5 and 9")
  {
    const unsignedbv_typet &unsigned_int = unsignedbv_typet(32);
    constant_interval_exprt five =
      constant_interval_exprt(from_integer(5, unsigned_int));
    constant_interval_exprt nine =
      constant_interval_exprt(from_integer(9, unsigned_int));

    constant_interval_exprt five_to_nine(
      from_integer(5, unsigned_int), from_integer(9, unsigned_int));

    THEN("Bitwise or should yield bitwise representation of 13")
    {
      REQUIRE(
        constant_interval_exprt::bitwise_or(five, nine) ==
        constant_interval_exprt(from_integer(13, unsigned_int)));

      REQUIRE(constant_interval_exprt::bitwise_or(five_to_nine, nine).is_top());
    }

    THEN("Bitwise and should yield bitwise representation of 1")
    {
      REQUIRE(
        constant_interval_exprt::bitwise_and(five, nine) ==
        constant_interval_exprt(from_integer(1, unsigned_int)));
      REQUIRE(
        (five & nine) ==
        constant_interval_exprt(from_integer(1, unsigned_int)));

      REQUIRE(
        constant_interval_exprt::bitwise_and(five_to_nine, nine).is_top());
    }

    THEN("Bitwise xor should yield bitwise representation of 12")
    {
      REQUIRE(
        constant_interval_exprt::bitwise_xor(five, nine) ==
        constant_interval_exprt(from_integer(12, unsigned_int)));

      REQUIRE(
        constant_interval_exprt::bitwise_xor(five_to_nine, nine).is_top());
    }
  }
}
