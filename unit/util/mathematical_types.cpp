/*******************************************************************\

Module: Unit test for util/mathematical_types.h

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/mathematical_types.h>
#include <util/std_expr.h>

#include <testing-utils/use_catch.h>

TEST_CASE("for an integer range", "[unit][util][mathematical_types]")
{
  SECTION("empty() returns true iff the range is empty")
  {
    // non-empty: from <= to
    REQUIRE(!integer_range_typet{1, 1}.empty());
    REQUIRE(!integer_range_typet{-5, 5}.empty());
    REQUIRE(!integer_range_typet{-10, -1}.empty());

    // empty: from > to
    REQUIRE(integer_range_typet{1, 0}.empty());
    REQUIRE(integer_range_typet{0, -1}.empty());
  }

  SECTION("size() returns the number of elements")
  {
    // singletons
    REQUIRE(integer_range_typet{1, 1}.size() == 1);
    REQUIRE(integer_range_typet{0, 0}.size() == 1);
    REQUIRE(integer_range_typet{-3, -3}.size() == 1);

    // standard ranges
    REQUIRE(integer_range_typet{0, 9}.size() == 10);
    REQUIRE(integer_range_typet{-5, 5}.size() == 11);
    REQUIRE(integer_range_typet{-10, -1}.size() == 10);

    // empty ranges clamp to 0
    REQUIRE(integer_range_typet{1, 0}.size() == 0);
    REQUIRE(integer_range_typet{5, -5}.size() == 0);

    // large values that exceed std::size_t
    const mp_integer large{"100000000000000000000"};
    REQUIRE(integer_range_typet{0, large}.size() == large + 1);
  }

  SECTION("from() / to() round-trip through the setters and getters")
  {
    integer_range_typet range{0, 0};
    range.from(-42);
    range.to(1000);
    REQUIRE(range.from() == -42);
    REQUIRE(range.to() == 1000);

    // large values are preserved
    const mp_integer large{"100000000000000000000"};
    range.from(-large);
    range.to(large);
    REQUIRE(range.from() == -large);
    REQUIRE(range.to() == large);
  }

  SECTION("includes() covers the closed interval and rejects outside values")
  {
    const integer_range_typet range{-3, 3};

    // interior
    REQUIRE(range.includes(0));
    REQUIRE(range.includes(1));
    REQUIRE(range.includes(-1));

    // boundaries are inclusive
    REQUIRE(range.includes(-3));
    REQUIRE(range.includes(3));

    // just outside
    REQUIRE(!range.includes(-4));
    REQUIRE(!range.includes(4));

    // empty range: nothing is included
    const integer_range_typet empty_range{1, 0};
    REQUIRE(!empty_range.includes(0));
    REQUIRE(!empty_range.includes(1));
    REQUIRE(!empty_range.includes(-1));
  }

  SECTION("zero_expr() / one_expr() succeed when 0 / 1 are in range")
  {
    const integer_range_typet range{-5, 5};
    const constant_exprt zero = range.zero_expr();
    REQUIRE(zero.type() == range);
    REQUIRE(zero.get_value() == ID_0);

    const constant_exprt one = range.one_expr();
    REQUIRE(one.type() == range);
    REQUIRE(one.get_value() == ID_1);
  }

  SECTION("zero_expr() / one_expr() fail PRECONDITIONs when out of range")
  {
    const cbmc_invariants_should_throwt invariants_throw_in_this_scope;

    // zero not included
    const integer_range_typet positive_range{1, 10};
    REQUIRE_THROWS_AS(positive_range.zero_expr(), invariant_failedt);
    // one is still included
    REQUIRE_NOTHROW(positive_range.one_expr());

    // one not included
    const integer_range_typet non_positive_range{-10, 0};
    REQUIRE_THROWS_AS(non_positive_range.one_expr(), invariant_failedt);
    // zero is still included
    REQUIRE_NOTHROW(non_positive_range.zero_expr());

    // empty range includes neither
    const integer_range_typet empty_range{1, 0};
    REQUIRE_THROWS_AS(empty_range.zero_expr(), invariant_failedt);
    REQUIRE_THROWS_AS(empty_range.one_expr(), invariant_failedt);
  }
}
