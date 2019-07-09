/*******************************************************************\

Module: Unit tests for interval_constraint in
        util/interval_constraint.cpp

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/interval_constraint.h>
#include <util/std_expr.h>
#include <util/std_types.h>

SCENARIO(
  "interval_constraint with characters",
  "[core][util][interval_constraint]")
{
  GIVEN("A string representing a character range and an character expression")
  {
    const integer_intervalt char_range('a', 'z');
    const exprt expr{"dummy", unsignedbv_typet(16)};

    WHEN("interval_constraint is called")
    {
      const auto result = interval_constraint(expr, char_range);

      THEN(
        "expect that the result is an and_exprt with two inequality "
        "expressions representing a <= expr && expr <= z")
      {
        REQUIRE(can_cast_expr<and_exprt>(result));

        REQUIRE(result.op0().id() == ID_ge);
        REQUIRE(result.op0().op0().type() == unsignedbv_typet(16));
        REQUIRE(can_cast_expr<constant_exprt>(result.op0().op1()));
        REQUIRE(to_constant_expr(result.op0().op1()).get_value() == "61"); // a

        REQUIRE(result.op1().id() == ID_le);
        REQUIRE(result.op1().op0().type() == unsignedbv_typet(16));
        REQUIRE(can_cast_expr<constant_exprt>(result.op1().op1()));
        REQUIRE(to_constant_expr(result.op1().op1()).get_value() == "7A"); // b
      }
    }
  }
}

SCENARIO(
  "interval_constraint with integers",
  "[core][util][interval_constraint]")
{
  GIVEN("A string representing a int range and an int expression")
  {
    const integer_intervalt int_range(6, 9);
    const exprt expr{"dummy", unsignedbv_typet(32)};

    WHEN("interval_constraint is called")
    {
      const auto result = interval_constraint(expr, int_range);

      THEN(
        "expect that the result is an and_exprt with two inequality "
        "expressions representing 6 <= expr && expr <= 9")
      {
        REQUIRE(can_cast_expr<and_exprt>(result));

        REQUIRE(result.op0().id() == ID_ge);
        REQUIRE(result.op0().op0().type() == unsignedbv_typet(32));
        REQUIRE(can_cast_expr<constant_exprt>(result.op0().op1()));
        REQUIRE(to_constant_expr(result.op0().op1()).get_value() == "6");

        REQUIRE(result.op1().id() == ID_le);
        REQUIRE(result.op1().op0().type() == unsignedbv_typet(32));
        REQUIRE(can_cast_expr<constant_exprt>(result.op1().op1()));
        REQUIRE(to_constant_expr(result.op1().op1()).get_value() == "9");
      }
    }
  }
}
