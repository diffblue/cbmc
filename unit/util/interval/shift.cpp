/*******************************************************************\
 Module: Unit tests for variable/sensitivity/abstract_object::merge
 Author: DiffBlue Limited
\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/interval.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#define V(X) (bvrep2integer(X.get(ID_value).c_str(), 32, true))
#define V_(X) (bvrep2integer(X.c_str(), 32, true))
#define CEV(X) (from_integer(mp_integer(X), signedbv_typet(32)))

SCENARIO("shift interval domain", "[core][analyses][interval][shift]")
{
  GIVEN("Two simple signed intervals")
  {
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    WHEN("Something")
    {
      THEN("Something else")
      {
        REQUIRE(
          constant_interval_exprt::left_shift(
            constant_interval_exprt(CEV(4), CEV(8)),
            constant_interval_exprt(CEV(1))) ==
          constant_interval_exprt(CEV(8), CEV(16)));
      }
    }
  }
}
