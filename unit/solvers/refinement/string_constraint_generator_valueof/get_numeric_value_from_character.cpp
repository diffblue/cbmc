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
  const typet char_type_1=unsignedbv_typet(8);
  const typet char_type_2=unsignedbv_typet(16);
  const typet char_type_3=unsignedbv_typet(32);
  const typet int_type_1=signedbv_typet(8);
  const typet int_type_2=signedbv_typet(16);
  const typet int_type_3=signedbv_typet(32);
  const typet int_type_4=signedbv_typet(64);
  symbol_tablet symtab;
  const namespacet ns(symtab);

  WHEN("0")
  {
    mp_integer character='0';
    mp_integer expected_value=0;
    const typet& char_type=char_type_1;
    const typet& int_type=int_type_1;
    constant_exprt expected_value_exprt=from_integer(expected_value, int_type);
    exprt actual_value_exprt=simplify_expr(
      get_numeric_value_from_character(
        from_integer(character, char_type), char_type, int_type),
      ns);
    REQUIRE(expected_value_exprt==actual_value_exprt);
  }
  WHEN("9")
  {
    mp_integer character='9';
    mp_integer expected_value=9;
    const typet& char_type=char_type_2;
    const typet& int_type=int_type_2;
    constant_exprt expected_value_exprt=from_integer(expected_value, int_type);
    exprt actual_value_exprt=simplify_expr(
      get_numeric_value_from_character(
        from_integer(character, char_type), char_type, int_type),
      ns);
    REQUIRE(expected_value_exprt==actual_value_exprt);
  }
  WHEN("A")
  {
    mp_integer character='A';
    mp_integer expected_value=10;
    const typet& char_type=char_type_3;
    const typet& int_type=int_type_3;
    constant_exprt expected_value_exprt=from_integer(expected_value, int_type);
    exprt actual_value_exprt=simplify_expr(
      get_numeric_value_from_character(
        from_integer(character, char_type), char_type, int_type),
      ns);
    REQUIRE(expected_value_exprt==actual_value_exprt);
  }
  WHEN("z")
  {
    mp_integer character='z';
    mp_integer expected_value=35;
    const typet& char_type=char_type_1;
    const typet& int_type=int_type_4;
    constant_exprt expected_value_exprt=from_integer(expected_value, int_type);
    exprt actual_value_exprt=simplify_expr(
      get_numeric_value_from_character(
        from_integer(character, char_type), char_type, int_type),
      ns);
    REQUIRE(expected_value_exprt==actual_value_exprt);
  }
  WHEN("+")
  {
    mp_integer character='+';
    mp_integer expected_value=0;
    const typet& char_type=char_type_2;
    const typet& int_type=int_type_1;
    constant_exprt expected_value_exprt=from_integer(expected_value, int_type);
    exprt actual_value_exprt=simplify_expr(
      get_numeric_value_from_character(
        from_integer(character, char_type), char_type, int_type),
      ns);
    REQUIRE(expected_value_exprt==actual_value_exprt);
  }
  WHEN("-")
  {
    mp_integer character='-';
    mp_integer expected_value=0;
    const typet& char_type=char_type_3;
    const typet& int_type=int_type_2;
    constant_exprt expected_value_exprt=from_integer(expected_value, int_type);
    exprt actual_value_exprt=simplify_expr(
      get_numeric_value_from_character(
        from_integer(character, char_type), char_type, int_type),
      ns);
    REQUIRE(expected_value_exprt==actual_value_exprt);
  }
}
