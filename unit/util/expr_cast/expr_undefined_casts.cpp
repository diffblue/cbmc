/*******************************************************************\

Module: Unit tests of expr_dynamic_cast

Author: Nathan Phillips <Nathan.Phillips@diffblue.com>

\*******************************************************************/

/// \file
/// expr_dynamic_cast for types that don't have a cast

// This could have a unit test that consisted of trying to compile the file
// and checking that the compiler gave the right error messages.

#include <testing-utils/use_catch.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>

SCENARIO("expr_dynamic_cast",
  "[core][utils][expr_cast][expr_dynamic_cast]")
{
  symbol_exprt symbol_expr;

  GIVEN("A const exprt reference to a symbolt")
  {
    const exprt &expr=symbol_expr;

    THEN("Casting from exprt reference to ieee_float_op_exprt "
         "should not compile")
    {
      // This shouldn't compile
      expr_dynamic_cast<const ieee_float_op_exprt &>(expr);
    }
    THEN("Casting from exprt reference to shift_exprt should not compile")
    {
      // This shouldn't compile
      expr_dynamic_cast<const shift_exprt &>(expr);
    }
    THEN(
      "Casting from exprt reference to non-reference should not compile")
    {
      // This shouldn't compile
      expr_dynamic_cast<symbol_exprt>(expr);
    }
    THEN(
      "Casting from const exprt reference to non-const symbol_exprt reference "
      "should not compile")
    {
      expr_dynamic_cast<symbol_exprt &>(expr);
    }
  }
}
