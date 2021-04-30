/*******************************************************************\
 Module: Unit tests for variable/sensitivity/abstract_object::merge
 Author: DiffBlue Limited
\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/interval.h>

#define V(X) (bvrep2integer(X.get(ID_value).c_str(), 32, true))
#define V_(X) (bvrep2integer(X.c_str(), 32, true))
#define CEV(X) (from_integer(mp_integer(X), signedbv_typet(32)))

TEST_CASE("shift interval domain", "[core][analyses][interval][shift]")
{
  SECTION("Left shift")
  {
    REQUIRE(
      constant_interval_exprt::left_shift(
        constant_interval_exprt(CEV(5)), constant_interval_exprt(CEV(1))) ==
      constant_interval_exprt(CEV(10)));

    const constant_interval_exprt four_to_eight(CEV(4), CEV(8));
    const constant_interval_exprt one(CEV(1));
    REQUIRE(
      constant_interval_exprt::left_shift(four_to_eight, one) ==
      constant_interval_exprt(CEV(8), CEV(16)));

    const constant_interval_exprt negative_one(CEV(-1));
    REQUIRE(constant_interval_exprt::left_shift(four_to_eight, negative_one)
              .is_top());
  }
  SECTION("Right shift")
  {
    REQUIRE(
      constant_interval_exprt::right_shift(
        constant_interval_exprt(CEV(5)), constant_interval_exprt(CEV(1))) ==
      constant_interval_exprt(CEV(2)));

    const constant_interval_exprt four_to_eight(CEV(4), CEV(8));
    const constant_interval_exprt one(CEV(1));
    REQUIRE(
      constant_interval_exprt::right_shift(four_to_eight, one) ==
      constant_interval_exprt(CEV(2), CEV(4)));

    const constant_interval_exprt negative_one(CEV(-1));
    REQUIRE(constant_interval_exprt::right_shift(four_to_eight, negative_one)
              .is_top());
  }
}
