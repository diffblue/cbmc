/*******************************************************************\
 Module: Unit tests for variable/sensitivity/abstract_object::merge
 Author: DiffBlue Limited
\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/arith_tools.h>
#include <util/interval.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#define V(X) (binary2integer(X.get(ID_value).c_str(), 2))
#define V_(X) (binary2integer(X.c_str(), 2))

SCENARIO("shift interval domain", "[core][analyses][interval][shift]")
{
  GIVEN("Two simple signed intervals")
  {
    const typet type = signedbv_typet(32);
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    source_locationt source_location;

    std::map<int, constant_exprt> v;

    for(int i = -100; i <= 100; i++)
    {
      v[i] = from_integer(mp_integer(i), type);
    }

    WHEN("Something")
    {
      THEN("Something else")
      {
        REQUIRE(
          constant_interval_exprt(v[4], v[8])
            .left_shift(constant_interval_exprt(v[1])) ==
          constant_interval_exprt(v[8], v[16]));
      }
    }
  }
}
