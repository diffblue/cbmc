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

SCENARIO("subtract interval domain", "[core][analyses][interval][subtract]")
{
  GIVEN("Two simple signed intervals")
  {
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    WHEN("The result is positive [6,8]-[2,4]")
    {
      constant_interval_exprt left(CEV(6), CEV(8));
      constant_interval_exprt right(CEV(2), CEV(4));

      constant_interval_exprt result =
        constant_interval_exprt::minus(left, right);

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
      constant_interval_exprt left(CEV(2), CEV(4));
      constant_interval_exprt right(CEV(6), max_exprt(signedbv_typet(32)));

      constant_interval_exprt result =
        constant_interval_exprt::minus(left, right);

      THEN("Domain is consistent")
      {
        REQUIRE(V(left.get_lower()) == 2);
        REQUIRE(V(left.get_upper()) == 4);
        REQUIRE(V(right.get_lower()) == 6);
        REQUIRE(right.has_no_upper_bound());
      }

      CAPTURE(result);

      THEN("The result is [MIN, -2]")
      {
        REQUIRE(V(result.get_upper()) == -2);
        REQUIRE(result.has_no_lower_bound());
      }
    }

    WHEN("Both contain infinite [2,INF]-[6,INF]")
    {
      constant_interval_exprt left(CEV(2), max_exprt(signedbv_typet(32)));
      constant_interval_exprt right(CEV(6), max_exprt(signedbv_typet(32)));

      constant_interval_exprt result =
        constant_interval_exprt::minus(left, right);

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

SCENARIO(
  "Subtracting unsigned integers",
  "[core][analyses][interval][subtract]")
{
  auto get_value = [](int x) { return from_integer(x, signedbv_typet(32)); };

  WHEN("Subtracting two constant intervals")
  {
    auto lhs = constant_interval_exprt(get_value(10));
    auto rhs = constant_interval_exprt(get_value(3));
    THEN("it should work")
    {
      auto result = constant_interval_exprt::minus(lhs, rhs);
      REQUIRE(result.is_single_value_interval());
      auto maybe_lower = numeric_cast<mp_integer>(result.get_lower());
      REQUIRE(maybe_lower.has_value());
      REQUIRE(maybe_lower.value() == 7);
    }
  }

  WHEN("Subtracting zero from something")
  {
    auto lhs = constant_interval_exprt(get_value(10));
    auto rhs = constant_interval_exprt(get_value(0));

    THEN("it should not give a completely crazy result")
    {
      auto result = constant_interval_exprt::minus(lhs, rhs);
      REQUIRE(result.is_single_value_interval());
      auto maybe_lower = numeric_cast<mp_integer>(result.get_lower());
      REQUIRE(maybe_lower.has_value());
      REQUIRE(maybe_lower.value() == 10);
    }
  }

  WHEN("Subtracting an non-constant interval containing zero")
  {
    auto lhs = constant_interval_exprt(get_value(10));
    auto rhs = constant_interval_exprt(get_value(0), get_value(1));
    THEN("it should not give a completely crazy result")
    {
      auto result = constant_interval_exprt::minus(lhs, rhs);
      auto maybe_lower = numeric_cast<mp_integer>(result.get_lower());
      REQUIRE(maybe_lower.has_value());
      REQUIRE(maybe_lower.value() == 9);
      auto maybe_upper = numeric_cast<mp_integer>(result.get_upper());
      REQUIRE(maybe_upper.has_value());
      REQUIRE(maybe_upper.value() == 10);
    }
  }
}
