/*******************************************************************\

Module: Unit test for expr.h/expr.cpp

Author: Diffblue Ltd

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr.h>
#include <util/std_types.h>

SCENARIO("bitfield-expr-is-zero", "[core][util][expr]")
{
  GIVEN("An exprt representing a bitfield constant of 3")
  {
    const exprt bitfield3 =
      from_integer(mp_integer(3), c_bit_field_typet(signedbv_typet(32), 4));

    THEN("is_zero() should be false")
    {
      REQUIRE_FALSE(bitfield3.is_zero());
    }
  }
  GIVEN("An exprt representing a bitfield constant of 0")
  {
    const exprt bitfield0 =
      from_integer(mp_integer(0), c_bit_field_typet(signedbv_typet(32), 4));

    THEN("is_zero() should be true")
    {
      REQUIRE(bitfield0.is_zero());
    }
  }
}

TEST_CASE("Bounded size is computer correctly", "[core][util][expr]")
{
  // Helper types and functions for constructing test expressions.
  const typet type = signedbv_typet(32);
  std::function<exprt(size_t)> make_expression;
  make_expression = [&](size_t size) -> exprt {
    PRECONDITION(size != 0);
    if(size <= 1)
      return from_integer(1, type);
    if(size == 2)
      return unary_minus_exprt(from_integer(1, type));
    return plus_exprt(from_integer(1, type), make_expression(size - 2));
  };
  // Actual test cases.
  REQUIRE(make_expression(1).bounded_size(10) == 1);
  REQUIRE(make_expression(2).bounded_size(10) == 2);
  REQUIRE(make_expression(3).bounded_size(10) == 3);

  REQUIRE(make_expression(30).bounded_size(10) < 13);
  REQUIRE(make_expression(30).bounded_size(10) >= 10);
}

TEST_CASE("Bounded size versus pathological example", "[core][util][expr]")
{
  const typet type = signedbv_typet(32);
  exprt pathology = plus_exprt(from_integer(1, type), from_integer(1, type));
  // Create an infinite exprt by self reference!
  pathology.add_to_operands(pathology);
  // If bounded size is not checking the bound this will never terminate.
  REQUIRE(pathology.bounded_size(10) < 13);
  REQUIRE(pathology.bounded_size(10) >= 10);
}
