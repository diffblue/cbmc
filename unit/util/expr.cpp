/*******************************************************************\

Module: Unit test for expr.h/expr.cpp

Author: Diffblue Ltd

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/c_types.h>

SCENARIO("bitfield-expr-is-zero", "[core][util][expr]")
{
  GIVEN("An exprt representing a bitfield constant of 3")
  {
    const exprt bitfield3 =
      from_integer(mp_integer(3), c_bit_field_typet(signedbv_typet(32), 4));

    THEN("is_zero() should be false")
    {
      REQUIRE_FALSE(bitfield3 == 0);
    }
  }
  GIVEN("An exprt representing a bitfield constant of 0")
  {
    const exprt bitfield0 =
      from_integer(mp_integer(0), c_bit_field_typet(signedbv_typet(32), 4));

    THEN("is_zero() should be true")
    {
      REQUIRE(bitfield0 == 0);
    }
  }
}

TEST_CASE(
  "exprt::visit_post handles deeply nested expressions",
  "[core][util][expr]")
{
  // visit_post is an iterative (explicit-stack) post-order traversal. A chain
  // this deep would overflow the call stack were it implemented recursively --
  // it is far beyond the depth at which recursion exceeds the default (~8 MiB)
  // unit-test stack -- yet light enough to stay cheap. Several rewrites rely on
  // visit_post for exactly this depth-safety (e.g. smt2_solvert's
  // expand_function_applications).
  const std::size_t depth = 100000;

  exprt e{ID_symbol};
  for(std::size_t i = 0; i < depth; ++i)
  {
    exprt parent{ID_typecast};
    parent.add_to_operands(std::move(e));
    e = std::move(parent);
  }

  std::size_t visited = 0;
  e.visit_post([&visited](exprt &) { ++visited; });

  // Dismantle the chain iteratively before it goes out of scope: this branch
  // does not include the depth-safe irept destructor, so destroying a chain
  // this deep recursively would overflow the stack.
  while(!e.operands().empty())
  {
    exprt child = std::move(e.operands().front());
    e = std::move(child);
  }

  REQUIRE(visited == depth + 1);
}
