/*
  Author: Nathan Phillips <Nathan.Phillips@diffblue.com>
*/

/// \file
/// expr_dynamic_cast Unit Tests

#include <catch.hpp>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/std_types.h>


SCENARIO("expr_dynamic_cast",
  "[core][utils][expr_cast][expr_dynamic_cast]")
{
  symbol_exprt symbol_expr;

  GIVEN("A const exprt pointer to a symbolt")
  {
    const exprt *expr_ptr=&symbol_expr;

    THEN("Casting from exprt pointer to symbol_exprt pointer returns non-null")
    {
      REQUIRE(expr_dynamic_cast<const symbol_exprt *>(expr_ptr)!=nullptr);
    }

    THEN("Casting from exprt pointer to transt pointer returns null")
    {
      REQUIRE(expr_dynamic_cast<const transt *>(expr_ptr)==nullptr);
    }
  }
  GIVEN("A exprt pointer to a symbolt")
  {
    exprt *expr_ptr=&symbol_expr;

    THEN("Casting from exprt pointer to symbol_exprt pointer returns non-null")
    {
      REQUIRE(expr_dynamic_cast<symbol_exprt *>(expr_ptr)!=nullptr);
    }

    THEN("Casting from exprt pointer to transt pointer returns null")
    {
      REQUIRE(expr_dynamic_cast<transt *>(expr_ptr)==nullptr);
    }
  }
  GIVEN("A const exprt reference to a symbolt")
  {
    const exprt &expr_ref=symbol_expr;

    THEN(
      "Casting from exprt reference to symbol_exprt reference should not throw")
    {
      REQUIRE_NOTHROW(expr_dynamic_cast<const symbol_exprt &>(expr_ref));
    }

    THEN("Casting from exprt reference to transt reference should throw")
    {
      // This no longer throws exceptions when our custom asserts are set to
      //  abort the program
      // REQUIRE_THROWS_AS(
      //   expr_dynamic_cast<const transt &>(expr_ref),
      //   std::bad_cast);
    }
  }
  GIVEN("A exprt reference to a symbolt")
  {
    exprt &expr_ref=symbol_expr;

    THEN(
      "Casting from exprt reference to symbol_exprt reference should not throw")
    {
      REQUIRE_NOTHROW(expr_dynamic_cast<symbol_exprt &>(expr_ref));
    }

    THEN("Casting from exprt reference to transt reference should throw")
    {
      // This no longer throws exceptions when our custom asserts are set to
      //  abort the program
      // REQUIRE_THROWS_AS(
      //   expr_dynamic_cast<transt &>(expr_ref),
      //   std::bad_cast);
    }

    THEN(
      "Casting from non-const exprt reference to const symbol_exprt reference "
      "should be fine")
    {
      REQUIRE_NOTHROW(expr_dynamic_cast<const symbol_exprt &>(expr_ref));
    }
  }
}
