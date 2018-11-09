/*******************************************************************\

Module: Unit tests for is_digit_with_radix in
        solvers/refinement/string_constraint_generator_valueof.cpp

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <solvers/strings/string_constraint_generator.h>

#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

/// Get the simplified return value of is_digit_with_radix called with a radix
static exprt actual(
  const mp_integer int_value,
  const exprt &radix_as_char,
  const unsigned long radix_ul,
  const bool strict_formatting)
{
  const typet char_type = unsignedbv_typet(16);
  const constant_exprt chr = from_integer(int_value, char_type);
  symbol_tablet symtab;
  const namespacet ns(symtab);

  return simplify_expr(
    is_digit_with_radix(chr, strict_formatting, radix_as_char, radix_ul), ns);
}

/// Get the simplified return value of is_digit_with_radix called with a radix
static exprt actual_with_radix(
  const mp_integer int_value,
  const unsigned long radix_ul,
  const bool strict_formatting)
{
  const typet char_type = unsignedbv_typet(16);
  const constant_exprt radix_as_char = from_integer(radix_ul, char_type);

  return actual(int_value, radix_as_char, radix_ul, strict_formatting);
}

/// Get the simplified return value of is_digit_with_radix called without a
/// radix
static exprt actual_without_radix(
  const mp_integer int_value,
  const unsigned long radix_ul,
  const bool strict_formatting)
{
  const typet char_type = unsignedbv_typet(16);
  const constant_exprt radix_as_char = from_integer(radix_ul, char_type);

  return actual(int_value, radix_as_char, 0, strict_formatting);
}

SCENARIO(
  "is_digit_with_radix without strict formatting",
  "[core][solvers][strings][string_constraint_generator_valueof]")
{
  WHEN("Radix 10")
  {
    const unsigned long radix_ul = 10;

    WHEN("char '0'")
    {
      WHEN("strict formatting on")
      {
        const bool strict = true;
        REQUIRE(true_exprt() == actual_without_radix('0', radix_ul, strict));
        REQUIRE(true_exprt() == actual_with_radix('0', radix_ul, strict));
      }
      WHEN("strict formatting off")
      {
        const bool strict = false;
        REQUIRE(true_exprt() == actual_without_radix('0', radix_ul, strict));
        REQUIRE(true_exprt() == actual_with_radix('0', radix_ul, strict));
      }
    }
    WHEN("char '9'")
    {
      WHEN("strict formatting on")
      {
        const bool strict = true;
        REQUIRE(true_exprt() == actual_without_radix('9', radix_ul, strict));
        REQUIRE(true_exprt() == actual_with_radix('9', radix_ul, strict));
      }
      WHEN("strict formatting off")
      {
        const bool strict = false;
        REQUIRE(true_exprt() == actual_without_radix('9', radix_ul, strict));
        REQUIRE(true_exprt() == actual_with_radix('9', radix_ul, strict));
      }
    }
    WHEN("char 'a'")
    {
      WHEN("strict formatting on")
      {
        const bool strict = true;
        REQUIRE(false_exprt() == actual_without_radix('a', radix_ul, strict));
        REQUIRE(false_exprt() == actual_with_radix('a', radix_ul, strict));
      }
      WHEN("strict formatting off")
      {
        const bool strict = false;
        REQUIRE(false_exprt() == actual_without_radix('a', radix_ul, strict));
        REQUIRE(false_exprt() == actual_with_radix('a', radix_ul, strict));
      }
    }
  }
  WHEN("Radix 8")
  {
    const unsigned long radix_ul = 8;

    WHEN("char '7'")
    {
      WHEN("strict formatting on")
      {
        const bool strict = true;
        REQUIRE(true_exprt() == actual_without_radix('7', radix_ul, strict));
        REQUIRE(true_exprt() == actual_with_radix('7', radix_ul, strict));
      }
      WHEN("strict formatting off")
      {
        const bool strict = false;
        REQUIRE(true_exprt() == actual_without_radix('7', radix_ul, strict));
        REQUIRE(true_exprt() == actual_with_radix('7', radix_ul, strict));
      }
    }
    WHEN("char '8'")
    {
      WHEN("strict formatting on")
      {
        const bool strict = true;
        REQUIRE(false_exprt() == actual_without_radix('8', radix_ul, strict));
        REQUIRE(false_exprt() == actual_with_radix('8', radix_ul, strict));
      }
      WHEN("strict formatting off")
      {
        const bool strict = false;
        REQUIRE(false_exprt() == actual_without_radix('8', radix_ul, strict));
        REQUIRE(false_exprt() == actual_with_radix('8', radix_ul, strict));
      }
    }
  }
  WHEN("Radix 16")
  {
    const unsigned long radix_ul = 16;

    WHEN("char '5'")
    {
      WHEN("strict formatting on")
      {
        const bool strict = true;
        REQUIRE(true_exprt() == actual_without_radix('5', radix_ul, strict));
        REQUIRE(true_exprt() == actual_with_radix('5', radix_ul, strict));
      }
      WHEN("strict formatting off")
      {
        const bool strict = false;
        REQUIRE(true_exprt() == actual_without_radix('5', radix_ul, strict));
        REQUIRE(true_exprt() == actual_with_radix('5', radix_ul, strict));
      }
    }
    WHEN("char 'a'")
    {
      WHEN("strict formatting on")
      {
        const bool strict = true;
        REQUIRE(true_exprt() == actual_without_radix('a', radix_ul, strict));
        REQUIRE(true_exprt() == actual_with_radix('a', radix_ul, strict));
      }
      WHEN("strict formatting off")
      {
        const bool strict = false;
        REQUIRE(true_exprt() == actual_without_radix('a', radix_ul, strict));
        REQUIRE(true_exprt() == actual_with_radix('a', radix_ul, strict));
      }
    }
    WHEN("char 'A'")
    {
      WHEN("strict formatting on")
      {
        const bool strict = true;
        REQUIRE(false_exprt() == actual_without_radix('A', radix_ul, strict));
        REQUIRE(false_exprt() == actual_with_radix('A', radix_ul, strict));
      }
      WHEN("strict formatting off")
      {
        const bool strict = false;
        REQUIRE(true_exprt() == actual_without_radix('A', radix_ul, strict));
        REQUIRE(true_exprt() == actual_with_radix('A', radix_ul, strict));
      }
    }
    WHEN("char 'f'")
    {
      WHEN("strict formatting on")
      {
        const bool strict = true;
        REQUIRE(true_exprt() == actual_without_radix('f', radix_ul, strict));
        REQUIRE(true_exprt() == actual_with_radix('f', radix_ul, strict));
      }
      WHEN("strict formatting off")
      {
        const bool strict = false;
        REQUIRE(true_exprt() == actual_without_radix('f', radix_ul, strict));
        REQUIRE(true_exprt() == actual_with_radix('f', radix_ul, strict));
      }
    }
    WHEN("char 'g'")
    {
      WHEN("strict formatting on")
      {
        const bool strict = true;
        REQUIRE(false_exprt() == actual_without_radix('g', radix_ul, strict));
        REQUIRE(false_exprt() == actual_with_radix('g', radix_ul, strict));
      }
      WHEN("strict formatting off")
      {
        const bool strict = false;
        REQUIRE(false_exprt() == actual_without_radix('g', radix_ul, strict));
        REQUIRE(false_exprt() == actual_with_radix('g', radix_ul, strict));
      }
    }
  }
}
