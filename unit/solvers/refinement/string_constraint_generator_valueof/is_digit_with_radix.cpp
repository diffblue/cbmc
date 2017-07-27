/*******************************************************************\

 Module: Unit tests for is_digit_with_radix in
   solvers/refinement/string_constraint_generator_valueof.cpp

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <catch.hpp>

#include <solvers/refinement/string_constraint_generator.h>
#include <util/namespace.h>
#include <util/symbol_table.h>
#include <util/simplify_expr.h>
#include <util/std_types.h>

SCENARIO("is_digit_with_radix",
  "[core][solvers][refinement][string_constraint_generator_valueof]")
{
  const typet char_type=unsignedbv_typet(16);
  symbol_tablet symtab;
  const namespacet ns(symtab);

  WHEN("Radix 10")
  {
    const constant_exprt radix_expr=from_integer(10, char_type);
    REQUIRE(true_exprt()==simplify_expr(
      is_digit_with_radix(from_integer('0', char_type), radix_expr), ns));
    REQUIRE(true_exprt()==simplify_expr(
      is_digit_with_radix(from_integer('9', char_type), radix_expr), ns));
    REQUIRE(false_exprt()==simplify_expr(
      is_digit_with_radix(from_integer('a', char_type), radix_expr), ns));
  }
  WHEN("Radix 8")
  {
    const constant_exprt radix_expr=from_integer(8, char_type);
    REQUIRE(true_exprt()==simplify_expr(
      is_digit_with_radix(from_integer('7', char_type), radix_expr), ns));
    REQUIRE(false_exprt()==simplify_expr(
      is_digit_with_radix(from_integer('8', char_type), radix_expr), ns));
  }
  WHEN("Radix 16")
  {
    const constant_exprt radix_expr=from_integer(16, char_type);
    REQUIRE(true_exprt()==simplify_expr(
      is_digit_with_radix(from_integer('a', char_type), radix_expr), ns));
    REQUIRE(true_exprt()==simplify_expr(
      is_digit_with_radix(from_integer('A', char_type), radix_expr), ns));
    REQUIRE(true_exprt()==simplify_expr(
      is_digit_with_radix(from_integer('f', char_type), radix_expr), ns));
    REQUIRE(false_exprt()==simplify_expr(
      is_digit_with_radix(from_integer('g', char_type), radix_expr), ns));
  }
}
