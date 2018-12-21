/*******************************************************************\

Module: Unit tests for get_numeric_value_from_character in
        solvers/refinement/string_constraint_generator_valueof.cpp

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <solvers/refinement/string_constraint_generator.h>
#include <util/namespace.h>
#include <util/symbol_table.h>
#include <util/simplify_expr.h>
#include <util/std_types.h>

/// Get the simplified return value of get_numeric_value_from_character called
/// with a radix
static exprt actual(
  const mp_integer &character,
  const typet &char_type,
  const typet &int_type,
  const bool strict_formatting,
  const unsigned long radix_ul)
{
  const constant_exprt chr=from_integer(character, char_type);
  symbol_tablet symtab;
  const namespacet ns(symtab);
  return simplify_expr(
    get_numeric_value_from_character(
      chr, char_type, int_type, strict_formatting, radix_ul),
    ns);
}

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

  WHEN("character='0'")
  {
    mp_integer character='0';
    mp_integer expected_mp=0;
    const typet& char_type=char_type_1;
    const typet& int_type=int_type_1;
    const constant_exprt expected=from_integer(expected_mp, int_type);

    REQUIRE(expected==actual(character, char_type, int_type, true, 0));
    REQUIRE(expected==actual(character, char_type, int_type, true, 36));
    REQUIRE(expected==actual(character, char_type, int_type, true, 10));
    REQUIRE(expected==actual(character, char_type, int_type, false, 0));
    REQUIRE(expected==actual(character, char_type, int_type, false, 36));
    REQUIRE(expected==actual(character, char_type, int_type, false, 10));
  }
  WHEN("character='9'")
  {
    mp_integer character='9';
    mp_integer expected_mp=9;
    const typet& char_type=char_type_2;
    const typet& int_type=int_type_2;
    const constant_exprt expected=from_integer(expected_mp, int_type);

    REQUIRE(expected==actual(character, char_type, int_type, true, 0));
    REQUIRE(expected==actual(character, char_type, int_type, true, 36));
    REQUIRE(expected==actual(character, char_type, int_type, true, 10));
    REQUIRE(expected==actual(character, char_type, int_type, false, 0));
    REQUIRE(expected==actual(character, char_type, int_type, false, 36));
    REQUIRE(expected==actual(character, char_type, int_type, false, 10));
  }
  WHEN("character='A'")
  {
    mp_integer character='A';
    mp_integer expected_mp=10;
    const typet& char_type=char_type_3;
    const typet& int_type=int_type_3;
    const constant_exprt expected=from_integer(expected_mp, int_type);

    REQUIRE(expected==actual(character, char_type, int_type, false, 0));
    REQUIRE(expected==actual(character, char_type, int_type, false, 36));
    REQUIRE(expected!=actual(character, char_type, int_type, false, 10));
  }
  WHEN("character='z'")
  {
    mp_integer character='z';
    mp_integer expected_mp=35;
    const typet& char_type=char_type_1;
    const typet& int_type=int_type_4;
    const constant_exprt expected=from_integer(expected_mp, int_type);

    REQUIRE(expected==actual(character, char_type, int_type, true, 0));
    REQUIRE(expected==actual(character, char_type, int_type, true, 36));
    REQUIRE(expected!=actual(character, char_type, int_type, true, 10));
    REQUIRE(expected==actual(character, char_type, int_type, false, 0));
    REQUIRE(expected==actual(character, char_type, int_type, false, 36));
    REQUIRE(expected!=actual(character, char_type, int_type, false, 10));
  }
  WHEN("character='+'")
  {
    mp_integer character='+';
    mp_integer expected_mp=0;
    const typet& char_type=char_type_2;
    const typet& int_type=int_type_1;
    const constant_exprt expected=from_integer(expected_mp, int_type);

    REQUIRE(expected==actual(character, char_type, int_type, true, 0));
    REQUIRE(expected==actual(character, char_type, int_type, true, 36));
    REQUIRE(expected==actual(character, char_type, int_type, true, 10));
    REQUIRE(expected==actual(character, char_type, int_type, false, 0));
    REQUIRE(expected==actual(character, char_type, int_type, false, 36));
    REQUIRE(expected==actual(character, char_type, int_type, false, 10));
  }
  WHEN("character='-'")
  {
    mp_integer character='-';
    mp_integer expected_mp=0;
    const typet& char_type=char_type_3;
    const typet& int_type=int_type_2;
    const constant_exprt expected=from_integer(expected_mp, int_type);

    REQUIRE(expected==actual(character, char_type, int_type, true, 0));
    REQUIRE(expected==actual(character, char_type, int_type, true, 36));
    REQUIRE(expected==actual(character, char_type, int_type, true, 10));
    REQUIRE(expected==actual(character, char_type, int_type, false, 0));
    REQUIRE(expected==actual(character, char_type, int_type, false, 36));
    REQUIRE(expected==actual(character, char_type, int_type, false, 10));
  }
}
