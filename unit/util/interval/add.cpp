/*******************************************************************\
 Module: Unit tests for variable/sensitivity/abstract_object::merge
 Author: DiffBlue Limited. All rights reserved.
\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/arith_tools.h>
#include <util/interval.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#define V(X) (binary2integer(X.get(ID_value).c_str(), 2))
#define V_(X) (binary2integer(X.c_str(), 2))

SCENARIO("add interval domain", "[core][analyses][interval][add]")
{
  GIVEN("Two simple signed intervals")
  {
    const typet type = signedbv_typet(32);
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    source_locationt source_location;

    std::map<int, constant_exprt> values;

    for(int i = -100; i <= 100; i++)
    {
      values[i] = from_integer(mp_integer(i), type);
    }

    WHEN("Both are positive [2,4]+[6,8]")
    {
      constant_interval_exprt left(values[2], values[4]);
      constant_interval_exprt right(values[6], values[8]);

      constant_interval_exprt result = left.plus(right);

      THEN("Domain is consistent")
      {
        REQUIRE(V(left.get_lower()) == 2);
        REQUIRE(V(left.get_upper()) == 4);
        REQUIRE(V(right.get_lower()) == 6);
        REQUIRE(V(right.get_upper()) == 8);
      }

      THEN("The result is [8, 12]")
      {
        REQUIRE(V(result.get_lower()) == 8);
        REQUIRE(V(result.get_upper()) == 12);
      }
    }

    WHEN("One contains infinite [2,4]+[6,INF]")
    {
      constant_interval_exprt left(values[2], values[4]);
      constant_interval_exprt right(values[6], max_exprt(type));

      constant_interval_exprt result = left.plus(right);

      THEN("Domain is consistent")
      {
        REQUIRE(V(left.get_lower()) == 2);
        REQUIRE(V(left.get_upper()) == 4);
        REQUIRE(V(right.get_lower()) == 6);
        REQUIRE(right.is_max());
      }

      CAPTURE(result);

      THEN("The result is [8, MAX]")
      {
        REQUIRE(V(result.get_lower()) == 8);
        REQUIRE(result.is_max());
      }
    }

    WHEN("Both contain infinite [2,INF]+[6,INF]")
    {
      constant_interval_exprt left(values[2], max_exprt(type));
      constant_interval_exprt right(values[6], max_exprt(type));

      constant_interval_exprt result = left.plus(right);

      THEN("Domain is consistent")
      {
        REQUIRE(V(left.get_lower()) == 2);
        REQUIRE(left.is_max());
        REQUIRE(V(right.get_lower()) == 6);
        REQUIRE(right.is_max());
      }

      CAPTURE(result);

      THEN("The result is [8, MAX]")
      {
        REQUIRE(V(result.get_lower()) == 8);
        REQUIRE(result.is_max());
      }
    }
  }
}
