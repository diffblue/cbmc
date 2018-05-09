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

SCENARIO("comparison interval domain", "[core][analyses][interval][comparison]")
{
  GIVEN("Two simple signed intervals")
  {
    const typet type = signedbv_typet(32);
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    const typet t = type;

    source_locationt source_location;

    std::map<int, constant_exprt> v;

    for(int i = -100; i <= 100; i++)
    {
      v[i] = from_integer(mp_integer(i), type);
    }

    WHEN("<, >, <=, >=, ==, != are tested on expressions")
    {
      THEN("Require correctness")
      {
        REQUIRE(constant_interval_exprt::less_than(v[0], v[1]));
        REQUIRE(constant_interval_exprt::less_than(v[1], v[2]));
        REQUIRE(constant_interval_exprt::less_than(v[1], v[100]));

        REQUIRE(constant_interval_exprt::less_than(v[-10], v[1]));
        REQUIRE_FALSE(constant_interval_exprt::less_than(v[-10], v[-100]));
        REQUIRE(constant_interval_exprt::less_than(v[-10], v[-5]));
        REQUIRE(constant_interval_exprt::less_than(v[-10], max_exprt(t)));
        REQUIRE(constant_interval_exprt::less_than(v[10], max_exprt(t)));
        REQUIRE(constant_interval_exprt::less_than(v[0], max_exprt(t)));

        REQUIRE_FALSE(constant_interval_exprt::less_than(v[-10], min_exprt(t)));
        REQUIRE_FALSE(constant_interval_exprt::less_than(v[10], min_exprt(t)));
        REQUIRE_FALSE(constant_interval_exprt::less_than(v[0], min_exprt(t)));

        REQUIRE_FALSE(
          constant_interval_exprt::less_than(min_exprt(t), min_exprt(t)));
        REQUIRE_FALSE(
          constant_interval_exprt::less_than(max_exprt(t), min_exprt(t)));
        REQUIRE_FALSE(
          constant_interval_exprt::less_than(max_exprt(t), max_exprt(t)));
        REQUIRE(constant_interval_exprt::less_than(min_exprt(t), max_exprt(t)));

        REQUIRE(constant_interval_exprt::equal(min_exprt(t), min_exprt(t)));
        REQUIRE(constant_interval_exprt::not_equal(max_exprt(t), min_exprt(t)));
        REQUIRE(constant_interval_exprt::equal(max_exprt(t), max_exprt(t)));
        REQUIRE(constant_interval_exprt::not_equal(min_exprt(t), max_exprt(t)));
      }

      THEN("")
      {
        REQUIRE_FALSE(constant_interval_exprt::greater_than(v[0], v[1]));
        REQUIRE_FALSE(constant_interval_exprt::greater_than(v[1], v[2]));
        REQUIRE_FALSE(constant_interval_exprt::greater_than(v[1], v[100]));

        REQUIRE_FALSE(constant_interval_exprt::greater_than(v[-10], v[1]));
        REQUIRE(constant_interval_exprt::greater_than(v[-10], v[-100]));
        REQUIRE_FALSE(constant_interval_exprt::greater_than(v[-10], v[-5]));
        REQUIRE_FALSE(
          constant_interval_exprt::greater_than(v[-10], max_exprt(t)));
        REQUIRE_FALSE(
          constant_interval_exprt::greater_than(v[10], max_exprt(t)));
        REQUIRE_FALSE(
          constant_interval_exprt::greater_than(v[0], max_exprt(t)));

        REQUIRE(constant_interval_exprt::greater_than(v[-10], min_exprt(t)));
        REQUIRE(constant_interval_exprt::greater_than(v[10], min_exprt(t)));
        REQUIRE(constant_interval_exprt::greater_than(v[0], min_exprt(t)));

        REQUIRE_FALSE(
          constant_interval_exprt::greater_than(min_exprt(t), min_exprt(t)));
        REQUIRE(constant_interval_exprt::greater_than_or_equal(
          min_exprt(t), min_exprt(t)));

        REQUIRE(
          constant_interval_exprt::greater_than(max_exprt(t), min_exprt(t)));
        REQUIRE(constant_interval_exprt::greater_than_or_equal(
          max_exprt(t), min_exprt(t)));

        REQUIRE_FALSE(
          constant_interval_exprt::greater_than(max_exprt(t), max_exprt(t)));

        REQUIRE_FALSE(
          constant_interval_exprt::greater_than(min_exprt(t), max_exprt(t)));
      }
    }

    WHEN("<, >, <=, >=, ==, != are tested on intervals")
    {
      THEN("Require correctness")
      {
        CHECK(
          constant_interval_exprt(v[10], v[20]) <
          constant_interval_exprt(v[30], v[40]));
        REQUIRE_FALSE(
          constant_interval_exprt(v[10], v[30]) <
          constant_interval_exprt(v[30], v[40]));
        REQUIRE_FALSE(
          constant_interval_exprt(v[10], v[20]) >
          constant_interval_exprt(v[30], v[40]));
      }

      THEN(
        "[10, 29] < [30, 40] == true, [10, 30] < [30, 40] == unknown, [10, 31] "
        "< [30, 40] == unknown")
      {
        CHECK(
          constant_interval_exprt(v[10], v[29])
            .less_than(constant_interval_exprt(v[30], v[40])) == tvt(true));
        CHECK(
          constant_interval_exprt(v[10], v[30])
            .less_than(constant_interval_exprt(v[30], v[40])) ==
          tvt::unknown());
        CHECK(
          constant_interval_exprt(v[10], v[31])
            .less_than(constant_interval_exprt(v[30], v[40])) ==
          tvt::unknown());

        CHECK(
          constant_interval_exprt(v[30], v[40])
            .less_than(constant_interval_exprt(v[10], v[29])) == tvt(false));
      }

      THEN(
        "[10, 29] > [30, 40] == false, [10, 30] > [30, 40] == unknown, [10, "
        "31] > [30, 40] == unknown")
      {
        CHECK(
          constant_interval_exprt(v[10], v[29])
            .greater_than(constant_interval_exprt(v[30], v[40])) == tvt(false));
        CHECK(
          constant_interval_exprt(v[10], v[29])
            .greater_than(constant_interval_exprt(v[30], v[40])) ==
          constant_interval_exprt(v[30], v[40])
            .less_than(constant_interval_exprt(v[10], v[29])));

        CHECK(
          constant_interval_exprt(v[10], v[30])
            .greater_than(constant_interval_exprt(v[30], v[40])) ==
          tvt::unknown());
        CHECK(
          constant_interval_exprt(v[10], v[31])
            .greater_than(constant_interval_exprt(v[30], v[40])) ==
          tvt::unknown());
      }

      THEN(
        "[10, 29] <= [30, 40] == true, [10, 30] <= [30, 40] == true, [10, 31] "
        "<- [30, 40] == unknown")
      {
        CHECK(
          constant_interval_exprt(v[10], v[29])
            .less_than_or_equal(constant_interval_exprt(v[30], v[40])) ==
          tvt(true));
        CHECK(
          constant_interval_exprt(v[10], v[30])
            .less_than_or_equal(constant_interval_exprt(v[30], v[40])) ==
          tvt(true));
        CHECK(
          constant_interval_exprt(v[10], v[31])
            .less_than_or_equal(constant_interval_exprt(v[30], v[40])) ==
          tvt::unknown());
      }

      THEN(
        "[10, 29] >= [30, 40] == false, [10, 30] >= [30, 40] == unknown, [10, "
        "31] >= [30, 40] == unknown")
      {
        CHECK(
          constant_interval_exprt(v[10], v[29])
            .greater_than_or_equal(constant_interval_exprt(v[30], v[40])) ==
          tvt(false));
        CHECK(
          constant_interval_exprt(v[10], v[30])
            .greater_than_or_equal(constant_interval_exprt(v[30], v[40])) ==
          tvt::unknown());
        CHECK(
          constant_interval_exprt(v[10], v[31])
            .greater_than_or_equal(constant_interval_exprt(v[30], v[40])) ==
          tvt::unknown());
      }
    }
  }
}
