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
  typet char_type=unsignedbv_typet(16);
  typet int_type=signedbv_typet(32);
  symbol_tablet symtab;
  namespacet ns(symtab);

  WHEN("Radix 10")
  {
    int radix=10;
    REQUIRE(true_exprt()==simplify_expr(
      is_digit_with_radix(
        from_integer('0', char_type),
        from_integer(radix, int_type)), ns));
    REQUIRE(true_exprt()==simplify_expr(
      is_digit_with_radix(
        from_integer('9', char_type),
        from_integer(radix, int_type)), ns));
    REQUIRE(false_exprt()==simplify_expr(
      is_digit_with_radix(
        from_integer('a', char_type),
        from_integer(radix, int_type)), ns));
  }
  WHEN("Radix 8")
  {
    int radix=8;
    REQUIRE(true_exprt()==simplify_expr(
      is_digit_with_radix(
        from_integer('7', char_type),
        from_integer(radix, int_type)), ns));
    REQUIRE(false_exprt()==simplify_expr(
      is_digit_with_radix(
        from_integer('8', char_type),
        from_integer(radix, int_type)), ns));
  }
  WHEN("Radix 16")
  {
    int radix=16;
    REQUIRE(true_exprt()==simplify_expr(
      is_digit_with_radix(
        from_integer('a', char_type),
        from_integer(radix, int_type)), ns));
    REQUIRE(true_exprt()==simplify_expr(
      is_digit_with_radix(
        from_integer('A', char_type),
        from_integer(radix, int_type)), ns));
    REQUIRE(true_exprt()==simplify_expr(
      is_digit_with_radix(
        from_integer('f', char_type),
        from_integer(radix, int_type)), ns));
    REQUIRE(false_exprt()==simplify_expr(
      is_digit_with_radix(
        from_integer('g', char_type),
        from_integer(radix, int_type)), ns));
  }
}
