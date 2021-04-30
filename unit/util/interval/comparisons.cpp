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

SCENARIO("comparison interval domain", "[core][analyses][interval][comparison]")
{
  GIVEN("Two simple signed intervals")
  {
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    WHEN("<, >, <=, >=, ==, != are tested on expressions")
    {
      THEN("Require correctness")
      {
        REQUIRE(constant_interval_exprt::less_than(CEV(0), CEV(1)));
        REQUIRE(constant_interval_exprt::less_than(CEV(1), CEV(2)));
        REQUIRE(constant_interval_exprt::less_than(CEV(1), CEV(100)));

        REQUIRE(constant_interval_exprt::less_than(CEV(-10), CEV(1)));
        REQUIRE_FALSE(constant_interval_exprt::less_than(CEV(-10), CEV(-100)));
        REQUIRE(constant_interval_exprt::less_than(CEV(-10), CEV(-5)));
        REQUIRE(constant_interval_exprt::less_than(
          CEV(-10), max_exprt(signedbv_typet(32))));
        REQUIRE(constant_interval_exprt::less_than(
          CEV(10), max_exprt(signedbv_typet(32))));
        REQUIRE(constant_interval_exprt::less_than(
          CEV(0), max_exprt(signedbv_typet(32))));

        REQUIRE_FALSE(constant_interval_exprt::less_than(
          CEV(-10), min_exprt(signedbv_typet(32))));
        REQUIRE_FALSE(constant_interval_exprt::less_than(
          CEV(10), min_exprt(signedbv_typet(32))));
        REQUIRE_FALSE(constant_interval_exprt::less_than(
          CEV(0), min_exprt(signedbv_typet(32))));

        REQUIRE_FALSE(constant_interval_exprt::less_than(
          min_exprt(signedbv_typet(32)), min_exprt(signedbv_typet(32))));
        REQUIRE_FALSE(constant_interval_exprt::less_than(
          max_exprt(signedbv_typet(32)), min_exprt(signedbv_typet(32))));
        REQUIRE_FALSE(constant_interval_exprt::less_than(
          max_exprt(signedbv_typet(32)), max_exprt(signedbv_typet(32))));
        REQUIRE(constant_interval_exprt::less_than(
          min_exprt(signedbv_typet(32)), max_exprt(signedbv_typet(32))));

        REQUIRE(constant_interval_exprt::equal(
          min_exprt(signedbv_typet(32)), min_exprt(signedbv_typet(32))));
        REQUIRE(constant_interval_exprt::not_equal(
          max_exprt(signedbv_typet(32)), min_exprt(signedbv_typet(32))));
        REQUIRE(constant_interval_exprt::equal(
          max_exprt(signedbv_typet(32)), max_exprt(signedbv_typet(32))));
        REQUIRE(constant_interval_exprt::not_equal(
          min_exprt(signedbv_typet(32)), max_exprt(signedbv_typet(32))));
      }

      THEN("")
      {
        REQUIRE_FALSE(constant_interval_exprt::greater_than(CEV(0), CEV(1)));
        REQUIRE_FALSE(constant_interval_exprt::greater_than(CEV(1), CEV(2)));
        REQUIRE_FALSE(constant_interval_exprt::greater_than(CEV(1), CEV(100)));

        REQUIRE_FALSE(constant_interval_exprt::greater_than(CEV(-10), CEV(1)));
        REQUIRE(constant_interval_exprt::greater_than(CEV(-10), CEV(-100)));
        REQUIRE_FALSE(constant_interval_exprt::greater_than(CEV(-10), CEV(-5)));
        REQUIRE_FALSE(constant_interval_exprt::greater_than(
          CEV(-10), max_exprt(signedbv_typet(32))));
        REQUIRE_FALSE(constant_interval_exprt::greater_than(
          CEV(10), max_exprt(signedbv_typet(32))));
        REQUIRE_FALSE(constant_interval_exprt::greater_than(
          CEV(0), max_exprt(signedbv_typet(32))));

        REQUIRE(constant_interval_exprt::greater_than(
          CEV(-10), min_exprt(signedbv_typet(32))));
        REQUIRE(constant_interval_exprt::greater_than(
          CEV(10), min_exprt(signedbv_typet(32))));
        REQUIRE(constant_interval_exprt::greater_than(
          CEV(0), min_exprt(signedbv_typet(32))));

        REQUIRE_FALSE(constant_interval_exprt::greater_than(
          min_exprt(signedbv_typet(32)), min_exprt(signedbv_typet(32))));
        REQUIRE(constant_interval_exprt::greater_than_or_equal(
          min_exprt(signedbv_typet(32)), min_exprt(signedbv_typet(32))));

        REQUIRE(constant_interval_exprt::greater_than(
          max_exprt(signedbv_typet(32)), min_exprt(signedbv_typet(32))));
        REQUIRE(constant_interval_exprt::greater_than_or_equal(
          max_exprt(signedbv_typet(32)), min_exprt(signedbv_typet(32))));

        REQUIRE_FALSE(constant_interval_exprt::greater_than(
          max_exprt(signedbv_typet(32)), max_exprt(signedbv_typet(32))));

        REQUIRE_FALSE(constant_interval_exprt::greater_than(
          min_exprt(signedbv_typet(32)), max_exprt(signedbv_typet(32))));
      }
    }

    WHEN("<, >, <=, >=, ==, != are tested on intervals")
    {
      THEN("Require correctness")
      {
        CHECK(
          constant_interval_exprt(CEV(10), CEV(20)) <
          constant_interval_exprt(CEV(30), CEV(40)));
        REQUIRE_FALSE(
          constant_interval_exprt(CEV(10), CEV(30)) <
          constant_interval_exprt(CEV(30), CEV(40)));
        REQUIRE_FALSE(
          constant_interval_exprt(CEV(10), CEV(20)) >
          constant_interval_exprt(CEV(30), CEV(40)));
        REQUIRE(
          constant_interval_exprt(CEV(10)) < constant_interval_exprt(CEV(30)));
      }

      THEN(
        "[10, 29] < [30, 40] == true, [10, 30] < [30, 40] == unknown, [10, 31] "
        "< [30, 40] == unknown")
      {
        CHECK(
          constant_interval_exprt(CEV(10), CEV(29))
            .less_than(constant_interval_exprt(CEV(30), CEV(40))) == tvt(true));
        CHECK(
          constant_interval_exprt(CEV(10), CEV(30))
            .less_than(constant_interval_exprt(CEV(30), CEV(40))) ==
          tvt::unknown());
        CHECK(
          constant_interval_exprt(CEV(10), CEV(31))
            .less_than(constant_interval_exprt(CEV(30), CEV(40))) ==
          tvt::unknown());

        CHECK(
          constant_interval_exprt(CEV(30), CEV(40))
            .less_than(constant_interval_exprt(CEV(10), CEV(29))) ==
          tvt(false));
      }

      THEN(
        "[10, 29] > [30, 40] == false, [10, 30] > [30, 40] == unknown, [10, "
        "31] > [30, 40] == unknown")
      {
        CHECK(
          constant_interval_exprt(CEV(10), CEV(29))
            .greater_than(constant_interval_exprt(CEV(30), CEV(40))) ==
          tvt(false));
        CHECK(
          constant_interval_exprt(CEV(10), CEV(29))
            .greater_than(constant_interval_exprt(CEV(30), CEV(40))) ==
          constant_interval_exprt(CEV(30), CEV(40))
            .less_than(constant_interval_exprt(CEV(10), CEV(29))));

        CHECK(
          constant_interval_exprt(CEV(10), CEV(30))
            .greater_than(constant_interval_exprt(CEV(30), CEV(40))) ==
          tvt::unknown());
        CHECK(
          constant_interval_exprt(CEV(10), CEV(31))
            .greater_than(constant_interval_exprt(CEV(30), CEV(40))) ==
          tvt::unknown());
      }

      THEN(
        "[10, 29] <= [30, 40] == true, [10, 30] <= [30, 40] == true, [10, 31] "
        "<- [30, 40] == unknown")
      {
        CHECK(
          constant_interval_exprt(CEV(10), CEV(29))
            .less_than_or_equal(constant_interval_exprt(CEV(30), CEV(40))) ==
          tvt(true));
        CHECK(
          constant_interval_exprt(CEV(10), CEV(30))
            .less_than_or_equal(constant_interval_exprt(CEV(30), CEV(40))) ==
          tvt(true));
        CHECK(
          constant_interval_exprt(CEV(10), CEV(31))
            .less_than_or_equal(constant_interval_exprt(CEV(30), CEV(40))) ==
          tvt::unknown());
        CHECK(constant_interval_exprt(CEV(10))
                .less_than_or_equal(constant_interval_exprt(CEV(30)))
                .is_true());
      }

      THEN(
        "[10, 29] >= [30, 40] == false, [10, 30] >= [30, 40] == unknown, [10, "
        "31] >= [30, 40] == unknown")
      {
        CHECK(
          constant_interval_exprt(CEV(10), CEV(29))
            .greater_than_or_equal(constant_interval_exprt(CEV(30), CEV(40))) ==
          tvt(false));
        CHECK(
          constant_interval_exprt(CEV(10), CEV(30))
            .greater_than_or_equal(constant_interval_exprt(CEV(30), CEV(40))) ==
          tvt::unknown());
        CHECK(
          constant_interval_exprt(CEV(10), CEV(31))
            .greater_than_or_equal(constant_interval_exprt(CEV(30), CEV(40))) ==
          tvt::unknown());
      }
      THEN("Intervals for truthyness")
      {
        constant_interval_exprt spans_zero(CEV(-1), CEV(1));
        REQUIRE(spans_zero.is_definitely_true().is_unknown());
        REQUIRE(spans_zero.is_definitely_false().is_unknown());

        constant_interval_exprt includes_zero_positive(CEV(0), CEV(1));
        REQUIRE(includes_zero_positive.is_definitely_true().is_unknown());
        REQUIRE(includes_zero_positive.is_definitely_false().is_unknown());

        constant_interval_exprt includes_zero_negative(CEV(-1), CEV(9));
        REQUIRE(includes_zero_negative.is_definitely_true().is_unknown());
        REQUIRE(includes_zero_negative.is_definitely_false().is_unknown());

        constant_interval_exprt zero(CEV(0));
        REQUIRE(zero.is_definitely_false().is_true());
        REQUIRE(zero.is_definitely_true().is_false());

        constant_interval_exprt positive_interval(CEV(1), CEV(5));
        REQUIRE(positive_interval.is_definitely_true().is_true());
        REQUIRE(positive_interval.is_definitely_false().is_false());

        constant_interval_exprt negative_interval(CEV(-5), CEV(-1));
        REQUIRE(negative_interval.is_definitely_true().is_true());
        REQUIRE(negative_interval.is_definitely_false().is_false());
      }
    }
  }
}

TEST_CASE("interval::equality", "[core][analyses][interval]")
{
  SECTION("Single element intervals")
  {
    constant_interval_exprt two(CEV(2));
    constant_interval_exprt four(CEV(4));

    REQUIRE_FALSE(two.equal(four).is_true());
    REQUIRE(two.equal(two).is_true());

    REQUIRE(two.not_equal(four).is_true());
    REQUIRE_FALSE(two.not_equal(two).is_true());
  }
  SECTION("Proper intervals")
  {
    constant_interval_exprt two_to_four(CEV(2), CEV(4));
    constant_interval_exprt six_to_eight(CEV(6), CEV(8));
    constant_interval_exprt five_to_ten(CEV(5), CEV(10));

    SECTION("Same interval")
    {
      // TODO: wrongly concludes that these are equal
      // ADA-537
      // REQUIRE(two_to_four.equal(two_to_four).is_unknown());
      // REQUIRE(two_to_four.not_equal(two_to_four).is_unknown());
    }
    SECTION("Overlapping intervals")
    {
      // TODO: wrongly concludes that these are not equal
      // ADA-537
      // REQUIRE_FALSE(six_to_eight.equal(five_to_ten).is_unknown());
      // REQUIRE_FALSE(six_to_eight.not_equal(five_to_ten).is_unknown());
    }
    SECTION("Disjoint intervals")
    {
      REQUIRE_FALSE(two_to_four.equal(six_to_eight).is_true());
      REQUIRE(two_to_four.not_equal(six_to_eight).is_true());
    }
  }
}
