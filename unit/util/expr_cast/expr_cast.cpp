/*******************************************************************\

Module: Unit tests of expr_dynamic_cast

Author: Nathan Phillips <Nathan.Phillips@diffblue.com>

\*******************************************************************/

/// \file
/// expr_dynamic_cast Unit Tests

#include <testing-utils/catch.hpp>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/std_types.h>


SCENARIO("expr_dynamic_cast",
  "[core][utils][expr_cast][expr_dynamic_cast]")
{
  symbol_exprt symbol_expr;

  GIVEN("A const exprt reference to a symbolt")
  {
    const exprt &expr=symbol_expr;

    THEN("Try-casting from exprt reference to symbol_exprt pointer "
         "returns a value")
    {
      REQUIRE(expr_try_dynamic_cast<symbol_exprt>(expr)!=nullptr);
    }

    THEN("Casting from exprt pointer to transt pointer doesn't return a value")
    {
      REQUIRE(expr_try_dynamic_cast<transt>(expr)==nullptr);
    }
  }
  GIVEN("A exprt reference to a symbolt")
  {
    exprt &expr=symbol_expr;

    THEN("Casting from exprt reference to symbol_exprt reference "
         "returns a value")
    {
      REQUIRE(expr_try_dynamic_cast<symbol_exprt>(expr)!=nullptr);
    }

    THEN("Casting from exprt reference to transt reference "
         "doesn't return a value")
    {
      REQUIRE(expr_try_dynamic_cast<transt>(expr)==nullptr);
    }
  }
  GIVEN("A const exprt reference to a symbolt")
  {
    const exprt &expr_ref=symbol_expr;

    THEN(
      "Casting from exprt reference to symbol_exprt reference should not throw")
    {
      REQUIRE_NOTHROW(expr_dynamic_cast<symbol_exprt>(expr_ref));
    }

    THEN("Casting from exprt reference to transt reference should throw")
    {
      // This no longer throws exceptions when our custom asserts are set to
      //  abort the program
      // REQUIRE_THROWS_AS(
      //   expr_dynamic_cast<transt>(expr_ref),
      //   std::bad_cast);
    }
  }
  GIVEN("A exprt reference to a symbolt")
  {
    exprt &expr_ref=symbol_expr;

    THEN(
      "Casting from exprt reference to symbol_exprt reference should not throw")
    {
      REQUIRE_NOTHROW(expr_dynamic_cast<symbol_exprt>(expr_ref));
    }

    THEN("Casting from exprt reference to transt reference should throw")
    {
      // This no longer throws exceptions when our custom asserts are set to
      //  abort the program
      // REQUIRE_THROWS_AS(
      //   expr_dynamic_cast<transt>(expr_ref),
      //   std::bad_cast);
    }

    THEN(
      "Casting from non-const exprt reference to const symbol_exprt reference "
      "should be fine")
    {
      REQUIRE_NOTHROW(expr_dynamic_cast<symbol_exprt>(expr_ref));
    }
  }
}
