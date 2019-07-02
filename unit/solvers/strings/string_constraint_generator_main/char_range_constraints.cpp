/*******************************************************************\

Module: Unit tests for char_range_constraints in
        solvers/refinement/string_constraint_generator_main.cpp

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <solvers/strings/string_constraint_generator.h>
#include <util/std_types.h>

SCENARIO(
  "char_range_constraints",
  "[core][solvers][strings][string_constraint_generator_main]")
{
  GIVEN("A string representing a character range and an character expression")
  {
    const std::string char_range = "a-z";
    const exprt expr{"dummy", unsignedbv_typet(16)};

    WHEN("char_range_constraints is called")
    {
      const auto result = char_range_constraints(expr, char_range);

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
