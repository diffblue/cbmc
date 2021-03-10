/*******************************************************************\
 Module: Unit tests for variable/sensitivity/abstract_object::merge
 Author: Diffblue Ltd.
\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/interval.h>

int value_of(const constant_interval_exprt &interval)
{
  REQUIRE(interval.is_single_value_interval());
  const auto value = numeric_cast<int>(interval.get_upper());
  REQUIRE(value.has_value());
  return *value;
}

bool matching_range(
  const constant_interval_exprt &actual,
  const constant_interval_exprt &expected)
{
  return actual.get_upper() == expected.get_upper() &&
         actual.get_lower() == expected.get_lower();
}

TEST_CASE("interval::divide", "[core][util][interval][divide]")
{
  cbmc_invariants_should_throwt invariants_throw;
  const signedbv_typet &signed_int_type = signedbv_typet(32);
  const auto zero = from_integer(0, signed_int_type);
  const auto one = from_integer(1, signed_int_type);
  const auto four = from_integer(4, signed_int_type);
  const auto eight = from_integer(8, signed_int_type);
  const auto negative_twelve = from_integer(-12, signed_int_type);
  const auto negative_sixteen = from_integer(-16, signed_int_type);

  SECTION("Single element intervals")
  {
    const constant_interval_exprt zero_interval(zero);
    const constant_interval_exprt one_interval(one);
    const constant_interval_exprt four_interval(four);
    const constant_interval_exprt eight_interval(eight);
    const constant_interval_exprt negative_twelve_interval(negative_twelve);

    REQUIRE(value_of(zero_interval.divide(four_interval)) == 0);
    REQUIRE(value_of(four_interval.divide(four_interval)) == 1);
    REQUIRE(value_of(four_interval.divide(eight_interval)) == 0);
    REQUIRE(value_of(eight_interval.divide(four_interval)) == 2);
    REQUIRE(value_of(negative_twelve_interval.divide(four_interval)) == -3);
    REQUIRE(value_of(negative_twelve_interval.divide(one_interval)) == -12);

    SECTION("Divide by zero")
    {
      // TODO: currently this triggers an invariant
      //       REQUIRE(zero_interval.divide(zero_interval).is_top());
      //       REQUIRE(one_interval.divide(zero_interval).is_top());
      //       REQUIRE(negative_twelve_interval.divide(zero_interval).is_top());
    }

    SECTION("Max & Min")
    {
      const constant_interval_exprt min_interval{min_exprt{signed_int_type}};
      const constant_interval_exprt max_interval{max_exprt{signed_int_type}};
      // TODO: division of single max or min don't work as expected
      // CHECK(max_interval.divide(max_interval).is_top());
      // CHECK(max_interval.divide(min_interval).is_top());
      CHECK(max_interval.divide(zero_interval).is_top());
      // CHECK(max_interval.divide(one_interval).is_top());

      // CHECK(min_interval.divide(max_interval).is_top());
      // CHECK(min_interval.divide(min_interval).is_top());
      CHECK(min_interval.divide(zero_interval).is_top());
      // CHECK(min_interval.divide(one_interval).is_top());
    }
  }

  SECTION("Interval ranges")
  {
    const constant_interval_exprt positive_range(four, eight);
    const constant_interval_exprt negative_range(
      negative_sixteen, negative_twelve);
    const constant_interval_exprt range_containing_zero(negative_twelve, four);
    const constant_interval_exprt zero_interval(zero);

    const constant_exprt &two = from_integer(2, signed_int_type);
    REQUIRE(matching_range(
      positive_range.divide(positive_range),
      constant_interval_exprt{zero, two}));

    REQUIRE(value_of(positive_range.divide(negative_range)) == 0);
    const constant_exprt &negative_four = from_integer(-4, signed_int_type);
    const constant_exprt &negative_one = from_integer(-1, signed_int_type);
    REQUIRE(matching_range(
      negative_range.divide(positive_range),
      constant_interval_exprt(negative_four, negative_one)));
  }
}
