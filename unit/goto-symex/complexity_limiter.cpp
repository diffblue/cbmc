/*******************************************************************\

Module: Unit test for goto-symex/complexity_limiter

Author: Diffblue Ltd

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>

#include <goto-symex/complexity_limiter.h>

TEST_CASE(
  "Bounded expression size is computed correctly",
  "[core][goto-symex][complexity_limiter]")
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
  REQUIRE(complexity_limitert::bounded_expr_size(make_expression(1), 10) == 1);
  REQUIRE(complexity_limitert::bounded_expr_size(make_expression(2), 10) == 2);
  REQUIRE(complexity_limitert::bounded_expr_size(make_expression(3), 10) == 3);

  REQUIRE(complexity_limitert::bounded_expr_size(make_expression(30), 10) < 13);
  REQUIRE(
    complexity_limitert::bounded_expr_size(make_expression(30), 10) >= 10);
}

TEST_CASE(
  "Bounded expression size versus pathological example",
  "[core][goto-symex][complexity_limiter]")
{
  const typet type = signedbv_typet(32);
  exprt pathology = plus_exprt(from_integer(1, type), from_integer(1, type));
  // Create an infinite exprt by self reference!
  pathology.add_to_operands(pathology);
  // If bounded expression size is not checking the bound this will never
  // terminate.
  REQUIRE(complexity_limitert::bounded_expr_size(pathology, 10) < 13);
  REQUIRE(complexity_limitert::bounded_expr_size(pathology, 10) >= 10);
}
