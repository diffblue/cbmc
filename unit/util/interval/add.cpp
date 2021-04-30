/*******************************************************************\
 Module: Unit tests for variable/sensitivity/abstract_object::merge
 Author: DiffBlue Limited
\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/interval.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

#define V(X) (bvrep2integer(X.get(ID_value).c_str(), 32, true))
#define V_(X) (bvrep2integer(X.c_str(), 32, true))
#define CEV(X) (from_integer(mp_integer(X), signedbv_typet(32)))

SCENARIO("add interval domain", "[core][analyses][interval][add]")
{
  GIVEN("Two simple signed intervals")
  {
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    WHEN("Both are positive [2,4]+[6,8]")
    {
      constant_interval_exprt left(CEV(2), CEV(4));
      constant_interval_exprt right(CEV(6), CEV(8));

      constant_interval_exprt result =
        constant_interval_exprt::plus(left, right);

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

      AND_WHEN("Incrementing the interval")
      {
        const auto incremented = left.increment();

        THEN("The result is correct")
        {
          REQUIRE(V(incremented.get_lower()) == 3);
          REQUIRE(V(incremented.get_upper()) == 5);
        }
      }
    }

    WHEN("One contains infinite [2,4]+[6,INF]")
    {
      constant_interval_exprt left(CEV(2), CEV(4));
      constant_interval_exprt right(CEV(6), max_exprt(signedbv_typet(32)));

      constant_interval_exprt result =
        constant_interval_exprt::plus(left, right);

      THEN("Domain is consistent")
      {
        REQUIRE(V(left.get_lower()) == 2);
        REQUIRE(V(left.get_upper()) == 4);
        REQUIRE(V(right.get_lower()) == 6);
        REQUIRE(right.has_no_upper_bound());
      }

      CAPTURE(result);

      THEN("The result is [8, MAX]")
      {
        REQUIRE(V(result.get_lower()) == 8);
        REQUIRE(result.has_no_upper_bound());
      }
    }

    WHEN("Both contain infinite [2,INF]+[6,INF]")
    {
      constant_interval_exprt left(CEV(2), max_exprt(signedbv_typet(32)));
      constant_interval_exprt right(CEV(6), max_exprt(signedbv_typet(32)));

      constant_interval_exprt result =
        constant_interval_exprt::plus(left, right);

      THEN("Domain is consistent")
      {
        REQUIRE(V(left.get_lower()) == 2);
        REQUIRE(left.has_no_upper_bound());
        REQUIRE(V(right.get_lower()) == 6);
        REQUIRE(right.has_no_upper_bound());
      }

      CAPTURE(result);

      THEN("The result is [8, MAX]")
      {
        REQUIRE(V(result.get_lower()) == 8);
        REQUIRE(result.has_no_upper_bound());
      }
    }
  }
}
