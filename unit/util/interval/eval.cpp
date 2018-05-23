/*******************************************************************\
 Module: Unit tests for intervals
 Author: DiffBlue Limited
\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/arith_tools.h>
#include <util/interval.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

SCENARIO("Unary eval on intervals", "[core][analyses][interval][eval]")
{
  WHEN("Negating a boolean interval")
  {
    constant_interval_exprt true_interval =
      constant_interval_exprt(true_exprt());
    constant_interval_exprt false_interval =
      constant_interval_exprt(false_exprt());
    constant_interval_exprt bool_top_interval =
      constant_interval_exprt(bool_typet());

    THEN("True interval negated should equal the false interval")
    {
      REQUIRE(true_interval.eval(ID_not) == false_interval);
    }
    THEN("False interval negated should equal the true interval")
    {
      REQUIRE(false_interval.eval(ID_not) == true_interval);
    }
    THEN("An unknown boolean type should equal top (itself)")
    {
      REQUIRE(bool_top_interval.eval(ID_not) == bool_top_interval);
    }
  }

  WHEN("Unary operations to an interval")
  {
    constant_interval_exprt five =
      constant_interval_exprt(from_integer(5, signedbv_typet(32)));

    THEN("When we apply unary addition to it, nothing should happen")
    {
      REQUIRE(five.eval(ID_unary_plus) == five);
    }

    THEN("When we apply unary subtraction to it, it should be negated")
    {
      auto negated_val =
        numeric_cast<mp_integer>(five.eval(ID_unary_minus).get_lower());
      REQUIRE(negated_val.has_value());
      REQUIRE(negated_val.value() == -5);
    }

    THEN("When we apply bitwise negation to it, is should be bitwise negated")
    {
      auto bitwise_negated_val =
        numeric_cast<mp_integer>(five.eval(ID_bitnot).get_lower());
      REQUIRE(bitwise_negated_val.has_value());
      REQUIRE(bitwise_negated_val.value() == (~5));
    }
  }
}
