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
}
