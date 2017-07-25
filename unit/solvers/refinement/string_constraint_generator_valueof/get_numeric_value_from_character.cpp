/*******************************************************************\

 Module: Unit tests for get_numeric_value_from_character in
   solvers/refinement/string_constraint_generator_valueof.cpp

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <catch.hpp>

#include <solvers/refinement/string_constraint_generator.h>
#include <util/namespace.h>
#include <util/symbol_table.h>
#include <util/simplify_expr.h>
#include <util/std_types.h>

SCENARIO("get_numeric_value_from_character",
  "[core][solvers][refinement][string_constraint_generator_valueof]")
{
  typet char_type=unsignedbv_typet(16);
  typet int_type=signedbv_typet(32);
  symbol_tablet symtab;
  namespacet ns(symtab);

  REQUIRE(from_integer(0, int_type)==simplify_expr(
    get_numeric_value_from_character(
      from_integer('0', char_type), char_type, int_type), ns));
  REQUIRE(from_integer(9, int_type)==simplify_expr(
    get_numeric_value_from_character(
      from_integer('9', char_type),
      char_type, int_type), ns));
  REQUIRE(from_integer(10, int_type)==simplify_expr(
    get_numeric_value_from_character(
      from_integer('A', char_type),
      char_type, int_type), ns));
  REQUIRE(from_integer(35, int_type)==simplify_expr(
    get_numeric_value_from_character(
      from_integer('z', char_type),
      char_type, int_type), ns));
}
