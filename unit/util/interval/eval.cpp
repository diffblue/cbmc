/*******************************************************************\
 Module: Unit tests for intervals
 Author: DiffBlue Limited
\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/interval.h>

SCENARIO("Unary eval on intervals", "[core][analyses][interval][eval]")
{
  WHEN("Negating a boolean interval")
  {
    constant_interval_exprt true_interval =
      constant_interval_exprt(true_exprt());
    constant_interval_exprt false_interval =
      constant_interval_exprt(false_exprt());
    constant_interval_exprt bool_top_interval =
      constant_interval_exprt(bool_typet());

    THEN("True interval negated should equal the false interval")
    {
      REQUIRE(true_interval.eval(ID_not) == false_interval);
    }
    THEN("False interval negated should equal the true interval")
    {
      REQUIRE(false_interval.eval(ID_not) == true_interval);
    }
    THEN("An unknown boolean type should equal top (itself)")
    {
      REQUIRE(bool_top_interval.eval(ID_not) == bool_top_interval);
    }
  }

  WHEN("Unary operations to an single element interval")
  {
    constant_interval_exprt five =
      constant_interval_exprt(from_integer(5, signedbv_typet(32)));
    const constant_interval_exprt &max_interval =
      constant_interval_exprt(max_exprt{signedbv_typet(32)});
    const constant_interval_exprt &min_interval =
      constant_interval_exprt(min_exprt{signedbv_typet(32)});

    THEN("When we apply unary addition to it, nothing should happen")
    {
      REQUIRE(five.eval(ID_unary_plus) == five);
      REQUIRE(min_interval.eval(ID_unary_plus).has_no_lower_bound());
      REQUIRE(max_interval.eval(ID_unary_plus).has_no_upper_bound());
    }

    THEN("When we apply unary subtraction to it, it should be negated")
    {
      auto negated_val =
        numeric_cast<mp_integer>(five.eval(ID_unary_minus).get_lower());
      REQUIRE(negated_val.has_value());
      REQUIRE(negated_val.value() == -5);

      // TODO: unary minus does not work on intervals that contain extremes
      // ADA-535
      // REQUIRE(max_interval.eval(ID_unary_minus).has_no_lower_bound());
      // REQUIRE(min_interval.eval(ID_unary_minus).has_no_upper_bound());
    }

    THEN("When we apply bitwise negation to it, is should be bitwise negated")
    {
      auto bitwise_negated_val =
        numeric_cast<mp_integer>(five.eval(ID_bitnot).get_lower());
      REQUIRE(bitwise_negated_val.has_value());
      REQUIRE(bitwise_negated_val.value() == (~5));
    }
  }
  WHEN("Unary operations to an single element interval")
  {
    constant_interval_exprt five_to_eight = constant_interval_exprt(
      from_integer(5, signedbv_typet(32)), from_integer(8, signedbv_typet(32)));

    THEN("When we apply unary addition to it, nothing should happen")
    {
      REQUIRE(five_to_eight.eval(ID_unary_plus) == five_to_eight);
    }

    THEN("When we apply unary minus to it, it should be negated")
    {
      const constant_interval_exprt &negated_value =
        five_to_eight.eval(ID_unary_minus);
      REQUIRE(
        negated_value ==
        constant_interval_exprt{from_integer(-8, signedbv_typet(32)),
                                from_integer(-5, signedbv_typet(32))});
    }

    THEN("When we apply bitwise negation to it, is should be bitwise negated")
    {
      // For intervals, bitwise not returns top
      REQUIRE(five_to_eight.eval(ID_bitnot).is_top());
    }
  }
}

TEST_CASE("binary eval switch", "[core][analyses][interval]")
{
  const auto interval_of = [](const int value) {
    return constant_interval_exprt(from_integer(value, signedbv_typet(32)));
  };

  const auto interval_from_to = [](const int lower, const int upper) {
    return constant_interval_exprt(
      from_integer(lower, signedbv_typet(32)),
      from_integer(upper, signedbv_typet(32)));
  };

  const auto boolean_interval = [](const bool value) {
    return constant_interval_exprt::tvt_to_interval(tvt(value));
  };

  constant_interval_exprt two = interval_of(2);
  constant_interval_exprt five = interval_of(5);
  constant_interval_exprt eight = interval_of(8);

  // Here we test only single element intervals, more robust testing of each
  // opertion can be found in the method unit tests (e.g.
  // unit/util/interval/add.cpp)

  SECTION("Numeric operations")
  {
    REQUIRE(five.eval(ID_plus, eight) == interval_of(13));
    REQUIRE(five.eval(ID_minus, eight) == interval_of(-3));
    REQUIRE(five.eval(ID_mult, eight) == interval_of(40));
    REQUIRE(five.eval(ID_div, eight) == interval_of(0));
    // Note modulo is implemented very imprecisely
    REQUIRE(five.eval(ID_mod, eight) == interval_from_to(0, 5));
    REQUIRE(five.eval(ID_shl, two) == interval_of(20 /* 5 << 2 */));
    REQUIRE(five.eval(ID_ashr, two) == interval_of(1 /* 5 >> 2 */));
    REQUIRE(five.eval(ID_bitor, eight) == interval_of(13));
    REQUIRE(five.eval(ID_bitand, eight) == interval_of(0));
    REQUIRE(five.eval(ID_bitxor, two) == interval_of(7));
  }
  SECTION("Comparisons")
  {
    REQUIRE(five.eval(ID_lt, eight) == boolean_interval(true));
    REQUIRE(five.eval(ID_le, eight) == boolean_interval(true));
    REQUIRE(five.eval(ID_gt, eight) == boolean_interval(false));
    REQUIRE(five.eval(ID_ge, eight) == boolean_interval(false));
    REQUIRE(five.eval(ID_equal, eight) == boolean_interval(false));
    REQUIRE(five.eval(ID_notequal, eight) == boolean_interval(true));
  }
  SECTION("Logical operators")
  {
    const auto true_interval = boolean_interval(true);
    const auto false_interval = boolean_interval(false);
    REQUIRE(
      true_interval.eval(ID_and, false_interval) == boolean_interval(false));
    REQUIRE(
      true_interval.eval(ID_or, false_interval) == boolean_interval(true));
    REQUIRE(
      true_interval.eval(ID_xor, false_interval) == boolean_interval(true));
  }
  SECTION("Invalid operations")
  {
    REQUIRE(five.eval(ID_type, eight).is_top());
  }
}
