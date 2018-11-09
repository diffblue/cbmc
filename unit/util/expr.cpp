/*******************************************************************\

Module: Unit test for expr.h/expr.cpp

Author: Diffblue Ltd

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>


SCENARIO("bitfield-expr-is-zero", "[core][util][expr]")
{
  GIVEN("An exprt representing a bitfield constant of 3")
  {
    const exprt bitfield3 =
      from_integer(mp_integer(3), c_bit_field_typet(signedbv_typet(32), 4));

    THEN("is_zero() should be false")
    {
      REQUIRE_FALSE(bitfield3.is_zero());
    }
  }
  GIVEN("An exprt representing a bitfield constant of 0")
  {
    const exprt bitfield0 =
      from_integer(mp_integer(0), c_bit_field_typet(signedbv_typet(32), 4));

    THEN("is_zero() should be true")
    {
      REQUIRE(bitfield0.is_zero());
    }
  }
}
