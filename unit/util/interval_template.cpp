/*******************************************************************\

Module: Unit tests for empty interval handling in interval_template.h

Author: Test suite for PR fixing empty interval handling

Description:
  Comprehensive unit tests for the empty interval handling fixes in
  interval_template.h. These tests validate:
  
  1. Empty interval comparisons (is_less_than, is_less_than_eq)
     - Lines 173-175, 184-186 of interval_template.h
  2. Empty interval operators (<=, ==, >=, <, >)
     - Lines 221-223, 253-255 of interval_template.h
  3. Empty interval union operations (approx_union_with, join)
     - Lines 195-204 of interval_template.h
  4. Empty interval intersection operations (intersect_with, meet)
  5. Edge cases with bounded intervals, singletons, and top intervals
  6. Consistency with mathematical conventions where empty set is a
     subset of every set and all empty sets are equal

  Test coverage includes:
  - Empty interval with empty interval operations
  - Empty interval with non-empty interval operations
  - Empty interval with singleton operations
  - Empty interval with top/unbounded interval operations
  - Empty interval with partially bounded intervals
  - Identity properties of empty intervals in unions
  - Consistency with is_bottom() method
  - Regression tests for previously failing scenarios

\*******************************************************************/

#include <util/integer_interval.h>
#include <util/mp_arith.h>

#include <testing-utils/use_catch.h>

SCENARIO(
  "empty interval comparison operations",
  "[core][util][interval_template][empty]")
{
  GIVEN("Two empty intervals")
  {
    // Create empty intervals: lower > upper
    integer_intervalt empty1(mp_integer(10), mp_integer(5));
    integer_intervalt empty2(mp_integer(20), mp_integer(15));

    REQUIRE(empty1.empty());
    REQUIRE(empty2.empty());

    WHEN("Testing is_less_than_eq with two empty intervals")
    {
      THEN("Empty intervals should be less than or equal to each other")
      {
        REQUIRE(empty1.is_less_than_eq(empty2));
        REQUIRE(empty2.is_less_than_eq(empty1));
      }
    }

    WHEN("Testing is_less_than with two empty intervals")
    {
      THEN("Empty intervals should be less than each other")
      {
        REQUIRE(empty1.is_less_than(empty2));
        REQUIRE(empty2.is_less_than(empty1));
      }
    }

    WHEN("Testing operator<= with two empty intervals")
    {
      THEN("Empty intervals should compare as less than or equal")
      {
        tvt result1 = empty1 <= empty2;
        tvt result2 = empty2 <= empty1;
        REQUIRE(result1.is_true());
        REQUIRE(result2.is_true());
      }
    }

    WHEN("Testing operator== with two empty intervals")
    {
      THEN("Empty intervals should be equal")
      {
        REQUIRE(empty1 == empty2);
      }
    }
  }

  GIVEN("An empty interval and a non-empty interval")
  {
    integer_intervalt empty(mp_integer(10), mp_integer(5));
    integer_intervalt non_empty(mp_integer(5), mp_integer(10));

    REQUIRE(empty.empty());
    REQUIRE_FALSE(non_empty.empty());

    WHEN("Testing is_less_than_eq")
    {
      THEN("Empty interval should be less than or equal to non-empty")
      {
        REQUIRE(empty.is_less_than_eq(non_empty));
      }

      THEN("Non-empty interval should be less than or equal to empty")
      {
        // Empty is treated as less than anything by convention
        REQUIRE(non_empty.is_less_than_eq(empty));
      }
    }

    WHEN("Testing is_less_than")
    {
      THEN("Empty interval should be less than non-empty")
      {
        REQUIRE(empty.is_less_than(non_empty));
      }

      THEN("Non-empty interval should be less than empty")
      {
        REQUIRE(non_empty.is_less_than(empty));
      }
    }

    WHEN("Testing operator<=")
    {
      THEN("Empty interval should compare as <= to non-empty")
      {
        tvt result = empty <= non_empty;
        REQUIRE(result.is_true());
      }

      THEN("Non-empty interval should compare as <= to empty")
      {
        tvt result = non_empty <= empty;
        REQUIRE(result.is_true());
      }
    }

    WHEN("Testing operator==")
    {
      THEN("Empty and non-empty intervals should not be equal")
      {
        REQUIRE_FALSE(empty == non_empty);
        REQUIRE_FALSE(non_empty == empty);
      }
    }
  }

  GIVEN("An empty interval and a singleton interval")
  {
    integer_intervalt empty(mp_integer(10), mp_integer(5));
    integer_intervalt singleton(mp_integer(7));

    REQUIRE(empty.empty());
    REQUIRE(singleton.singleton());

    WHEN("Testing is_less_than_eq")
    {
      THEN("Empty interval should be less than or equal to singleton")
      {
        REQUIRE(empty.is_less_than_eq(singleton));
      }

      THEN("Singleton should be less than or equal to empty")
      {
        REQUIRE(singleton.is_less_than_eq(empty));
      }
    }

    WHEN("Testing is_less_than")
    {
      THEN("Empty interval should be less than singleton")
      {
        REQUIRE(empty.is_less_than(singleton));
      }

      THEN("Singleton should be less than empty")
      {
        REQUIRE(singleton.is_less_than(empty));
      }
    }

    WHEN("Testing operator<=")
    {
      THEN("Comparisons should return true")
      {
        REQUIRE((empty <= singleton).is_true());
        REQUIRE((singleton <= empty).is_true());
      }
    }
  }

  GIVEN("An empty interval and a top interval (unbounded)")
  {
    integer_intervalt empty(mp_integer(10), mp_integer(5));
    integer_intervalt top; // Default constructor creates top

    REQUIRE(empty.empty());
    REQUIRE(top.is_top());

    WHEN("Testing is_less_than_eq")
    {
      THEN("Empty interval should be less than or equal to top")
      {
        REQUIRE(empty.is_less_than_eq(top));
      }

      THEN("Top should be less than or equal to empty")
      {
        REQUIRE(top.is_less_than_eq(empty));
      }
    }

    WHEN("Testing operator<=")
    {
      THEN("Comparisons should return true")
      {
        REQUIRE((empty <= top).is_true());
        REQUIRE((top <= empty).is_true());
      }
    }
  }
}

SCENARIO(
  "empty interval union operations",
  "[core][util][interval_template][empty][union]")
{
  GIVEN("An empty interval and a non-empty interval")
  {
    integer_intervalt empty(mp_integer(10), mp_integer(5));
    integer_intervalt interval(mp_integer(5), mp_integer(15));

    REQUIRE(empty.empty());
    REQUIRE_FALSE(interval.empty());

    WHEN("Union of non-empty interval with empty interval")
    {
      integer_intervalt result = interval;
      result.approx_union_with(empty);

      THEN("Result should be the non-empty interval")
      {
        REQUIRE(result == interval);
        REQUIRE(result.get_lower() == mp_integer(5));
        REQUIRE(result.get_upper() == mp_integer(15));
      }
    }

    WHEN("Union of empty interval with non-empty interval")
    {
      integer_intervalt result = empty;
      result.approx_union_with(interval);

      THEN("Result should be the non-empty interval")
      {
        REQUIRE(result == interval);
        REQUIRE(result.get_lower() == mp_integer(5));
        REQUIRE(result.get_upper() == mp_integer(15));
      }
    }
  }

  GIVEN("Two empty intervals")
  {
    integer_intervalt empty1(mp_integer(10), mp_integer(5));
    integer_intervalt empty2(mp_integer(20), mp_integer(15));

    REQUIRE(empty1.empty());
    REQUIRE(empty2.empty());

    WHEN("Union of two empty intervals")
    {
      integer_intervalt result = empty1;
      result.approx_union_with(empty2);

      THEN("Result should remain empty")
      {
        // The result should be empty1 unchanged since empty2 is empty
        REQUIRE(result.empty());
      }
    }
  }

  GIVEN("An empty interval and a singleton")
  {
    integer_intervalt empty(mp_integer(10), mp_integer(5));
    integer_intervalt singleton(mp_integer(7));

    REQUIRE(empty.empty());
    REQUIRE(singleton.singleton());

    WHEN("Union of empty with singleton")
    {
      integer_intervalt result = empty;
      result.approx_union_with(singleton);

      THEN("Result should be the singleton")
      {
        REQUIRE(result == singleton);
        REQUIRE(result.singleton());
        REQUIRE(result.get_lower() == mp_integer(7));
        REQUIRE(result.get_upper() == mp_integer(7));
      }
    }

    WHEN("Union of singleton with empty")
    {
      integer_intervalt result = singleton;
      result.approx_union_with(empty);

      THEN("Result should be the singleton")
      {
        REQUIRE(result == singleton);
        REQUIRE(result.singleton());
      }
    }
  }

  GIVEN("An empty interval and a top interval")
  {
    integer_intervalt empty(mp_integer(10), mp_integer(5));
    integer_intervalt top;

    REQUIRE(empty.empty());
    REQUIRE(top.is_top());

    WHEN("Union of empty with top")
    {
      integer_intervalt result = empty;
      result.approx_union_with(top);

      THEN("Result should be top")
      {
        REQUIRE(result.is_top());
      }
    }

    WHEN("Union of top with empty")
    {
      integer_intervalt result = top;
      result.approx_union_with(empty);

      THEN("Result should be top")
      {
        REQUIRE(result.is_top());
      }
    }
  }

  GIVEN("Two disjoint non-empty intervals")
  {
    integer_intervalt interval1(mp_integer(0), mp_integer(5));
    integer_intervalt interval2(mp_integer(10), mp_integer(15));

    REQUIRE_FALSE(interval1.empty());
    REQUIRE_FALSE(interval2.empty());

    WHEN("Computing their union")
    {
      integer_intervalt result = interval1;
      result.approx_union_with(interval2);

      THEN("Result should span from min to max of both intervals")
      {
        REQUIRE(result.get_lower() == mp_integer(0));
        REQUIRE(result.get_upper() == mp_integer(15));
      }
    }
  }
}

SCENARIO(
  "empty interval intersection operations",
  "[core][util][interval_template][empty][intersection]")
{
  GIVEN("An empty interval and a non-empty interval")
  {
    integer_intervalt empty(mp_integer(10), mp_integer(5));
    integer_intervalt interval(mp_integer(5), mp_integer(15));

    REQUIRE(empty.empty());
    REQUIRE_FALSE(interval.empty());

    WHEN("Intersection of empty with non-empty")
    {
      integer_intervalt result = empty;
      result.intersect_with(interval);

      THEN("Result should be empty")
      {
        REQUIRE(result.empty());
      }
    }

    WHEN("Intersection of non-empty with empty")
    {
      integer_intervalt result = interval;
      result.intersect_with(empty);

      THEN("Result should become empty")
      {
        REQUIRE(result.empty());
      }
    }
  }

  GIVEN("Two empty intervals")
  {
    integer_intervalt empty1(mp_integer(10), mp_integer(5));
    integer_intervalt empty2(mp_integer(20), mp_integer(15));

    REQUIRE(empty1.empty());
    REQUIRE(empty2.empty());

    WHEN("Intersection of two empty intervals")
    {
      integer_intervalt result = empty1;
      result.intersect_with(empty2);

      THEN("Result should be empty")
      {
        REQUIRE(result.empty());
      }
    }
  }

  GIVEN("Two overlapping non-empty intervals")
  {
    integer_intervalt interval1(mp_integer(0), mp_integer(10));
    integer_intervalt interval2(mp_integer(5), mp_integer(15));

    REQUIRE_FALSE(interval1.empty());
    REQUIRE_FALSE(interval2.empty());

    WHEN("Computing their intersection")
    {
      integer_intervalt result = interval1;
      result.intersect_with(interval2);

      THEN("Result should be the overlap")
      {
        REQUIRE_FALSE(result.empty());
        REQUIRE(result.get_lower() == mp_integer(5));
        REQUIRE(result.get_upper() == mp_integer(10));
      }
    }
  }

  GIVEN("Two disjoint non-empty intervals")
  {
    integer_intervalt interval1(mp_integer(0), mp_integer(5));
    integer_intervalt interval2(mp_integer(10), mp_integer(15));

    REQUIRE_FALSE(interval1.empty());
    REQUIRE_FALSE(interval2.empty());

    WHEN("Computing their intersection")
    {
      integer_intervalt result = interval1;
      result.intersect_with(interval2);

      THEN("Result should be empty")
      {
        REQUIRE(result.empty());
      }
    }
  }
}

SCENARIO(
  "empty interval edge cases",
  "[core][util][interval_template][empty][edge_cases]")
{
  GIVEN("An empty interval created by make_bottom")
  {
    integer_intervalt interval;
    interval.make_bottom();

    REQUIRE(interval.is_bottom());
    REQUIRE(interval.empty());

    WHEN("Testing comparisons with another empty interval")
    {
      integer_intervalt other_empty(mp_integer(10), mp_integer(5));

      THEN("They should be equal")
      {
        REQUIRE(interval == other_empty);
      }

      THEN("Comparison operators should work correctly")
      {
        REQUIRE((interval <= other_empty).is_true());
        REQUIRE((other_empty <= interval).is_true());
      }
    }

    WHEN("Testing union with a non-empty interval")
    {
      integer_intervalt non_empty(mp_integer(1), mp_integer(10));
      integer_intervalt result = interval;
      result.approx_union_with(non_empty);

      THEN("Result should be the non-empty interval")
      {
        REQUIRE(result == non_empty);
      }
    }
  }

  GIVEN("Multiple empty intervals with different bounds")
  {
    integer_intervalt empty1(mp_integer(100), mp_integer(50));
    integer_intervalt empty2(mp_integer(5), mp_integer(3));
    integer_intervalt empty3(mp_integer(-10), mp_integer(-20));

    REQUIRE(empty1.empty());
    REQUIRE(empty2.empty());
    REQUIRE(empty3.empty());

    WHEN("Testing equality")
    {
      THEN("All empty intervals should be equal regardless of bounds")
      {
        REQUIRE(empty1 == empty2);
        REQUIRE(empty2 == empty3);
        REQUIRE(empty1 == empty3);
      }
    }

    WHEN("Testing comparisons")
    {
      THEN("All empty intervals should be <= each other")
      {
        REQUIRE((empty1 <= empty2).is_true());
        REQUIRE((empty2 <= empty3).is_true());
        REQUIRE((empty3 <= empty1).is_true());
      }
    }
  }

  GIVEN("An interval that becomes empty after operations")
  {
    integer_intervalt interval(mp_integer(0), mp_integer(10));
    REQUIRE_FALSE(interval.empty());

    WHEN("Making it less than itself when it's a singleton")
    {
      integer_intervalt singleton(mp_integer(5));
      integer_intervalt other = singleton;

      singleton.make_less_than(other);

      THEN("Both intervals should become bottom (empty)")
      {
        REQUIRE(singleton.empty());
        REQUIRE(other.empty());
      }
    }

    WHEN("Intersecting with a disjoint interval")
    {
      integer_intervalt disjoint(mp_integer(20), mp_integer(30));
      interval.intersect_with(disjoint);

      THEN("Result should be empty")
      {
        REQUIRE(interval.empty());
      }

      WHEN("Then comparing this empty result")
      {
        integer_intervalt another(mp_integer(5), mp_integer(10));

        THEN("Empty interval should be <= any interval")
        {
          REQUIRE((interval <= another).is_true());
        }

        THEN("Empty interval should be equal to other empty intervals")
        {
          integer_intervalt another_empty(mp_integer(1), mp_integer(0));
          REQUIRE(interval == another_empty);
        }
      }
    }
  }
}

SCENARIO(
  "empty interval with bounded intervals",
  "[core][util][interval_template][empty][bounds]")
{
  GIVEN("An empty interval and intervals with only lower or upper bounds")
  {
    integer_intervalt empty(mp_integer(10), mp_integer(5));
    REQUIRE(empty.empty());

    WHEN("Testing with a lower-bounded interval")
    {
      integer_intervalt lower_bounded;
      lower_bounded.lower_set = true;
      lower_bounded.lower = mp_integer(0);
      lower_bounded.upper_set = false;

      REQUIRE_FALSE(lower_bounded.is_top());
      REQUIRE_FALSE(lower_bounded.empty());

      THEN("Empty should compare as <= to lower-bounded")
      {
        REQUIRE((empty <= lower_bounded).is_true());
      }

      THEN("Union of empty with lower-bounded should be lower-bounded")
      {
        integer_intervalt result = empty;
        result.approx_union_with(lower_bounded);
        REQUIRE(result.lower_set);
        REQUIRE(result.lower == mp_integer(0));
        REQUIRE_FALSE(result.upper_set);
      }
    }

    WHEN("Testing with an upper-bounded interval")
    {
      integer_intervalt upper_bounded;
      upper_bounded.lower_set = false;
      upper_bounded.upper_set = true;
      upper_bounded.upper = mp_integer(10);

      REQUIRE_FALSE(upper_bounded.is_top());
      REQUIRE_FALSE(upper_bounded.empty());

      THEN("Empty should compare as <= to upper-bounded")
      {
        REQUIRE((empty <= upper_bounded).is_true());
      }

      THEN("Union of empty with upper-bounded should be upper-bounded")
      {
        integer_intervalt result = empty;
        result.approx_union_with(upper_bounded);
        REQUIRE_FALSE(result.lower_set);
        REQUIRE(result.upper_set);
        REQUIRE(result.upper == mp_integer(10));
      }
    }
  }
}

TEST_CASE(
  "empty interval consistency with is_bottom",
  "[core][util][interval_template][empty]")
{
  SECTION("empty() and is_bottom() should be equivalent")
  {
    integer_intervalt empty_interval(mp_integer(10), mp_integer(5));
    REQUIRE(empty_interval.empty());
    REQUIRE(empty_interval.is_bottom());
    REQUIRE(empty_interval.empty() == empty_interval.is_bottom());
  }

  SECTION("make_bottom() should create an empty interval")
  {
    integer_intervalt interval;
    interval.make_bottom();
    REQUIRE(interval.empty());
    REQUIRE(interval.is_bottom());
  }

  SECTION("Non-empty intervals should not be bottom")
  {
    integer_intervalt non_empty(mp_integer(5), mp_integer(10));
    REQUIRE_FALSE(non_empty.empty());
    REQUIRE_FALSE(non_empty.is_bottom());
  }

  SECTION("Top interval should not be bottom")
  {
    integer_intervalt top;
    REQUIRE_FALSE(top.empty());
    REQUIRE_FALSE(top.is_bottom());
    REQUIRE(top.is_top());
  }
}

TEST_CASE(
  "empty interval operator!= behavior",
  "[core][util][interval_template][empty]")
{
  SECTION("Two empty intervals should not be != each other")
  {
    integer_intervalt empty1(mp_integer(10), mp_integer(5));
    integer_intervalt empty2(mp_integer(20), mp_integer(15));

    REQUIRE(empty1 == empty2);
    REQUIRE_FALSE(empty1 != empty2);
  }

  SECTION("Empty and non-empty should be !=")
  {
    integer_intervalt empty(mp_integer(10), mp_integer(5));
    integer_intervalt non_empty(mp_integer(5), mp_integer(10));

    REQUIRE_FALSE(empty == non_empty);
    REQUIRE(empty != non_empty);
  }
}

SCENARIO(
  "empty interval with join and meet operations",
  "[core][util][interval_template][empty][join_meet]")
{
  GIVEN("An empty interval and a non-empty interval")
  {
    integer_intervalt empty(mp_integer(10), mp_integer(5));
    integer_intervalt interval(mp_integer(5), mp_integer(15));

    REQUIRE(empty.empty());
    REQUIRE_FALSE(interval.empty());

    WHEN("Performing join (union) operation")
    {
      integer_intervalt result1 = empty;
      result1.join(interval);

      THEN("Result should be the non-empty interval")
      {
        REQUIRE(result1 == interval);
      }

      integer_intervalt result2 = interval;
      result2.join(empty);

      THEN("Result should be the non-empty interval (commutative)")
      {
        REQUIRE(result2 == interval);
      }
    }

    WHEN("Performing meet (intersection) operation")
    {
      integer_intervalt result1 = empty;
      result1.meet(interval);

      THEN("Result should be empty")
      {
        REQUIRE(result1.empty());
      }

      integer_intervalt result2 = interval;
      result2.meet(empty);

      THEN("Result should be empty (commutative)")
      {
        REQUIRE(result2.empty());
      }
    }
  }

  GIVEN("Two empty intervals")
  {
    integer_intervalt empty1(mp_integer(10), mp_integer(5));
    integer_intervalt empty2(mp_integer(20), mp_integer(15));

    REQUIRE(empty1.empty());
    REQUIRE(empty2.empty());

    WHEN("Performing join operation")
    {
      integer_intervalt result = empty1;
      result.join(empty2);

      THEN("Result should remain empty")
      {
        REQUIRE(result.empty());
      }
    }

    WHEN("Performing meet operation")
    {
      integer_intervalt result = empty1;
      result.meet(empty2);

      THEN("Result should remain empty")
      {
        REQUIRE(result.empty());
      }
    }
  }
}

SCENARIO(
  "empty interval comparisons with operators",
  "[core][util][interval_template][empty][operators]")
{
  GIVEN("Various interval types")
  {
    integer_intervalt empty(mp_integer(10), mp_integer(5));
    integer_intervalt non_empty(mp_integer(5), mp_integer(15));
    integer_intervalt singleton(mp_integer(10));

    REQUIRE(empty.empty());
    REQUIRE_FALSE(non_empty.empty());
    REQUIRE(singleton.singleton());

    WHEN("Testing operator>= with empty intervals")
    {
      THEN("Empty >= Empty should be true")
      {
        tvt result = empty >= empty;
        REQUIRE(result.is_true());
      }

      THEN("Empty >= Non-empty should be true")
      {
        tvt result = empty >= non_empty;
        REQUIRE(result.is_true());
      }

      THEN("Non-empty >= Empty should be true")
      {
        tvt result = non_empty >= empty;
        REQUIRE(result.is_true());
      }
    }

    WHEN("Testing operator< with empty intervals")
    {
      THEN("Empty < Empty should be false (negation of >=)")
      {
        tvt result = empty < empty;
        // operator< is defined as !(a>=b)
        REQUIRE(result.is_false());
      }

      THEN("Empty < Non-empty should be false")
      {
        tvt result = empty < non_empty;
        REQUIRE(result.is_false());
      }
    }

    WHEN("Testing operator> with empty intervals")
    {
      THEN("Empty > Empty should be false (negation of <=)")
      {
        tvt result = empty > empty;
        // operator> is defined as !(a<=b)
        REQUIRE(result.is_false());
      }

      THEN("Empty > Non-empty should be false")
      {
        tvt result = empty > non_empty;
        REQUIRE(result.is_false());
      }
    }
  }
}

SCENARIO(
  "empty interval boundary operations",
  "[core][util][interval_template][empty][boundary]")
{
  GIVEN("An empty interval")
  {
    integer_intervalt empty(mp_integer(10), mp_integer(5));
    REQUIRE(empty.empty());

    WHEN("Attempting to add bounds to empty interval")
    {
      integer_intervalt result = empty;
      result.make_le_than(mp_integer(3));

      THEN("It should still be empty but with updated upper bound")
      {
        REQUIRE(result.upper_set);
        REQUIRE(result.upper == mp_integer(3)); // min of 5 and 3
        // Still empty because lower (10) > upper (3) is false, but already was
        REQUIRE(result.empty());
      }
    }

    WHEN("Creating empty interval from make_bottom and testing bounds")
    {
      integer_intervalt bottom_empty;
      bottom_empty.make_bottom();

      THEN("Should be empty with specific properties")
      {
        REQUIRE(bottom_empty.empty());
        REQUIRE(bottom_empty.lower_set);
        REQUIRE(bottom_empty.upper_set);
        // make_bottom sets upper = T() and lower = upper + 1
        REQUIRE(bottom_empty.lower > bottom_empty.upper);
      }
    }
  }
}

TEST_CASE(
  "empty interval regression tests",
  "[core][util][interval_template][empty][regression]")
{
  SECTION("Previously failing case: empty interval union identity")
  {
    // Empty interval should act as identity element for union
    integer_intervalt empty(mp_integer(100), mp_integer(50));
    integer_intervalt interval(mp_integer(0), mp_integer(10));

    integer_intervalt result = interval;
    result.approx_union_with(empty);

    REQUIRE(result == interval);
    REQUIRE(result.get_lower() == mp_integer(0));
    REQUIRE(result.get_upper() == mp_integer(10));
  }

  SECTION("Previously failing case: all empty intervals are equal")
  {
    // Regardless of the actual bounds, all empty intervals should be equal
    integer_intervalt empty1(mp_integer(1), mp_integer(0));
    integer_intervalt empty2(mp_integer(1000), mp_integer(-1000));
    integer_intervalt empty3(mp_integer(-5), mp_integer(-10));

    REQUIRE(empty1 == empty2);
    REQUIRE(empty2 == empty3);
    REQUIRE(empty1 == empty3);
  }

  SECTION("Previously failing case: empty interval comparisons")
  {
    // Empty intervals should be considered less than or equal to everything
    integer_intervalt empty(mp_integer(10), mp_integer(5));
    integer_intervalt interval(mp_integer(20), mp_integer(30));

    REQUIRE(empty.is_less_than_eq(interval));
    REQUIRE(empty.is_less_than(interval));
    REQUIRE((empty <= interval).is_true());
  }

  SECTION("Empty interval should not affect union of two non-empty intervals")
  {
    integer_intervalt interval1(mp_integer(0), mp_integer(5));
    integer_intervalt interval2(mp_integer(10), mp_integer(15));
    integer_intervalt empty(mp_integer(100), mp_integer(50));

    // Union of interval1 and interval2
    integer_intervalt result1 = interval1;
    result1.approx_union_with(interval2);

    // Union of interval1, interval2, and empty
    integer_intervalt result2 = interval1;
    result2.approx_union_with(interval2);
    result2.approx_union_with(empty);

    // Should be the same
    REQUIRE(result1 == result2);
  }
}
