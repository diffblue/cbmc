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

SCENARIO("subtract interval domain", "[core][analyses][interval][subtract]")
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

    WHEN("The result is positive [6,8]-[2,4]")
    {
      constant_interval_exprt left(values[6], values[8]);
      constant_interval_exprt right(values[2], values[4]);

      constant_interval_exprt result = left.minus(right);

      THEN("Domain is consistent")
      {
        REQUIRE(V(left.get_lower()) == 6);
        REQUIRE(V(left.get_upper()) == 8);
        REQUIRE(V(right.get_lower()) == 2);
        REQUIRE(V(right.get_upper()) == 4);
      }

      THEN("The result is [2, 6]")
      {
        REQUIRE(V(result.get_lower()) == 2);
        REQUIRE(V(result.get_upper()) == 6);
      }
    }

    WHEN("One contains infinite [2,4]-[6,INF]")
    {
      constant_interval_exprt left(values[2], values[4]);
      constant_interval_exprt right(values[6], max_exprt(type));

      constant_interval_exprt result = left.minus(right);

      THEN("Domain is consistent")
      {
        REQUIRE(V(left.get_lower()) == 2);
        REQUIRE(V(left.get_upper()) == 4);
        REQUIRE(V(right.get_lower()) == 6);
        REQUIRE(right.is_max());
      }

      CAPTURE(result);

      THEN("The result is [MIN, -2]")
      {
        REQUIRE(V(result.get_upper()) == -2);
        REQUIRE(result.is_min());
      }
    }

    WHEN("Both contain infinite [2,INF]-[6,INF]")
    {
      constant_interval_exprt left(values[2], max_exprt(type));
      constant_interval_exprt right(values[6], max_exprt(type));

      constant_interval_exprt result = left.minus(right);

      THEN("Domain is consistent")
      {
        REQUIRE(V(left.get_lower()) == 2);
        REQUIRE(left.has_no_upper_bound());
        REQUIRE(V(right.get_lower()) == 6);
        REQUIRE(right.has_no_upper_bound());
      }

      CAPTURE(result);

      THEN("The result is [MIN, MAX]")
      {
        REQUIRE(result.has_no_upper_bound());
        REQUIRE(result.has_no_lower_bound());
      }
    }
  }
}

SCENARIO("Subtracting unsigned integers")
{
  WHEN("Subtracting two constant intervals")
  {
    auto lhs =
      constant_interval_exprt(constant_exprt("1010", unsignedbv_typet(32)));
    auto rhs =
      constant_interval_exprt(constant_exprt("0011", unsignedbv_typet(32)));
    THEN("it should work")
    {
      auto result = lhs.minus(rhs);
      REQUIRE(result.is_single_value_interval());
      auto maybe_lower = numeric_cast<mp_integer>(result.get_lower());
      REQUIRE(maybe_lower.has_value());
      REQUIRE(maybe_lower.value() == 7);
    }
  }

  WHEN("Subtracting zero from something")
  {
    auto lhs =
      constant_interval_exprt(constant_exprt("1010", unsignedbv_typet(32)));
    auto rhs =
      constant_interval_exprt(constant_exprt("0", unsignedbv_typet(32)));

    THEN("it should not give a completely crazy result")
    {
      auto result = lhs.minus(rhs);
      REQUIRE(result.is_single_value_interval());
      auto maybe_lower = numeric_cast<mp_integer>(result.get_lower());
      REQUIRE(maybe_lower.has_value());
      REQUIRE(maybe_lower.value() == 10);
    }
  }

  WHEN("Subtracting an non-constant interval containing zero")
  {
    auto lhs =
      constant_interval_exprt(constant_exprt("1010", unsignedbv_typet(32)));
    auto rhs = constant_interval_exprt(
      constant_exprt("0", unsignedbv_typet(32)),
      constant_exprt("1", unsignedbv_typet(32)));
    THEN("it should not give a completely crazy result")
    {
      auto result = lhs.minus(rhs);
      auto maybe_lower = numeric_cast<mp_integer>(result.get_lower());
      REQUIRE(maybe_lower.has_value());
      REQUIRE(maybe_lower.value() == 9);
      auto maybe_upper = numeric_cast<mp_integer>(result.get_upper());
      REQUIRE(maybe_upper.has_value());
      REQUIRE(maybe_upper.value() == 10);
    }
  }
}