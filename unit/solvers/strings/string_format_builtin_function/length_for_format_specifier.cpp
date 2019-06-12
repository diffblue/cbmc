/*******************************************************************\

Module: Unit tests for length_for_format_specifier
        solvers/refinement/string_format_builtin_function.cpp

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <solvers/strings/format_specifier.h>
#include <solvers/strings/string_format_builtin_function.h>
#include <util/range.h>
#include <util/simplify_expr.h>
#include <util/string_expr.h>
#include <util/symbol_table.h>

// Create array_string_exprt from array of characters
array_string_exprt from_char_vector(
  std::vector<mp_integer> string_array,
  const typet &char_type,
  const typet &length_type,
  const pointer_typet &pointer_type,
  array_poolt &array_pool)
{
  const array_typet array_type(
    char_type, from_integer(string_array.size(), length_type));
  const std::vector<exprt> expr_array =
    make_range(string_array).map([&](const mp_integer el) {
      return from_integer(el, char_type);
    });
  const array_exprt array(expr_array, array_type);
  const exprt first_element = index_exprt(array, from_integer(0, length_type));
  const exprt pointer = address_of_exprt(first_element, pointer_type);
  const array_string_exprt arg = array_pool.find(pointer, array_type.size());
  array_pool.insert(pointer, arg); // really necessary?
  return arg;
}

SCENARIO(
  "length_for_format_specifier",
  "[core][solvers][strings][string_format_builtin_function]")
{
  const typet char_type = unsignedbv_typet(16);
  const typet length_type = signedbv_typet(32);
  const std::size_t pointer_width = 16;
  const auto pointer_type = pointer_typet(char_type, pointer_width);

  const symbol_tablet symbol_table;
  const namespacet ns{symbol_table};
  symbol_generatort fresh_symbol;
  array_poolt array_pool{fresh_symbol};

  WHEN("format specifier = %s")
  {
    WHEN("arg = serialized(\"bar\")")
    {
      array_string_exprt arg = from_char_vector(
        {'b', 'a', 'r'}, char_type, length_type, pointer_type, array_pool);
      format_specifiert fs{0, "", 0, 0, false, format_specifiert::STRING};
      const exprt actual =
        length_for_format_specifier(fs, arg, length_type, array_pool);
      THEN("length constraint represents 3")
      {
        int to_int = *numeric_cast<int>(to_constant_expr(actual));
        REQUIRE(to_int == 3);
      }
    }
  }

  WHEN("format specifier = %d")
  {
    WHEN("arg = serialized(12)")
    {
      const array_string_exprt arg = from_char_vector(
        {0, 0, 0, 12}, char_type, length_type, pointer_type, array_pool);
      format_specifiert fs{
        0, "", 0, 0, false, format_specifiert::DECIMAL_INTEGER};
      const exprt actual =
        length_for_format_specifier(fs, arg, length_type, array_pool);
      const exprt simpl_actual = simplify_expr(actual, ns);
      THEN("length constraint represents 2")
      {
        const int to_int = *numeric_cast<int>(to_constant_expr(simpl_actual));
        REQUIRE(to_int == 2);
      }
    }
  }

  WHEN("format specifier = %d")
  {
    WHEN("arg = serialized(-12)")
    {
      const array_string_exprt arg = from_char_vector(
        {0xFFFF, 0xFFFF, 0xFFFF, 0xFFF4},
        char_type,
        length_type,
        pointer_type,
        array_pool);
      format_specifiert fs{
        0, "", 0, 0, false, format_specifiert::DECIMAL_INTEGER};
      const exprt actual =
        length_for_format_specifier(fs, arg, length_type, array_pool);
      const exprt simpl_actual = simplify_expr(actual, ns);
      THEN("length constraint represents 2")
      {
        const int to_int = *numeric_cast<int>(to_constant_expr(simpl_actual));
        REQUIRE(to_int == 3);
      }
    }
  }

  WHEN("format specifier = %d")
  {
    WHEN("arg = serialized(-1234567890)")
    {
      const array_string_exprt arg = from_char_vector(
        {0xFFFF, 0xFFFF, 0xB669, 0xFD2E},
        char_type,
        length_type,
        pointer_type,
        array_pool);
      format_specifiert fs{
        0, "", 0, 0, false, format_specifiert::DECIMAL_INTEGER};
      const exprt actual =
        length_for_format_specifier(fs, arg, length_type, array_pool);
      const exprt simpl_actual = simplify_expr(actual, ns);
      THEN("length constraint represents 11")
      {
        const int to_int = *numeric_cast<int>(to_constant_expr(simpl_actual));
        REQUIRE(to_int == 11);
      }
    }
  }

  WHEN("format specifier = %d")
  {
    WHEN("arg = serialized(null)")
    {
      const array_string_exprt arg = from_char_vector(
        {'n', 'u', 'l', 'l'}, char_type, length_type, pointer_type, array_pool);
      format_specifiert fs{
        0, "", 0, 0, false, format_specifiert::DECIMAL_INTEGER};
      const exprt actual =
        length_for_format_specifier(fs, arg, length_type, array_pool);
      const exprt simpl_actual = simplify_expr(actual, ns);
      THEN("length constraint represents 4")
      {
        const int to_int = *numeric_cast<int>(to_constant_expr(simpl_actual));
        REQUIRE(to_int == 4);
      }
    }
  }

  WHEN("format specifier = %x")
  {
    WHEN("arg = serialized(12)")
    {
      const array_string_exprt arg = from_char_vector(
        {0, 0, 0, 12}, char_type, length_type, pointer_type, array_pool);
      format_specifiert fs{
        0, "", 0, 0, false, format_specifiert::HEXADECIMAL_INTEGER};
      const exprt actual =
        length_for_format_specifier(fs, arg, length_type, array_pool);
      const exprt simpl_actual = simplify_expr(actual, ns);
      THEN("length constraint represents 1")
      {
        const int to_int = *numeric_cast<int>(to_constant_expr(simpl_actual));
        REQUIRE(to_int == 1);
      }
    }
  }

  WHEN("format specifier = %c")
  {
    WHEN("arg = serialized('c')")
    {
      const array_string_exprt arg = from_char_vector(
        {0, 0, 0, 'c'}, char_type, length_type, pointer_type, array_pool);
      format_specifiert fs{0, "", 0, 0, false, format_specifiert::CHARACTER};
      const exprt actual =
        length_for_format_specifier(fs, arg, length_type, array_pool);
      const exprt simpl_actual = simplify_expr(actual, ns);
      THEN("length constraint represents 1")
      {
        const int to_int = *numeric_cast<int>(to_constant_expr(simpl_actual));
        REQUIRE(to_int == 1);
      }
    }
  }

  WHEN("format specifier = %c")
  {
    WHEN("arg = serialized(null)")
    {
      const array_string_exprt arg = from_char_vector(
        {'n', 'u', 'l', 'l'}, char_type, length_type, pointer_type, array_pool);
      format_specifiert fs{0, "", 0, 0, false, format_specifiert::CHARACTER};
      const exprt actual =
        length_for_format_specifier(fs, arg, length_type, array_pool);
      const exprt simpl_actual = simplify_expr(actual, ns);
      THEN("length constraint represents 4")
      {
        const int to_int = *numeric_cast<int>(to_constant_expr(simpl_actual));
        REQUIRE(to_int == 4);
      }
    }
  }

  WHEN("format specifier = %b")
  {
    WHEN("arg = serialized(false)")
    {
      const array_string_exprt arg = from_char_vector(
        {0, 0, 0, 0}, char_type, length_type, pointer_type, array_pool);
      format_specifiert fs{0, "", 0, 0, false, format_specifiert::BOOLEAN};
      const exprt actual =
        length_for_format_specifier(fs, arg, length_type, array_pool);
      const exprt simpl_actual = simplify_expr(actual, ns);
      THEN("length constraint represents 5")
      {
        const int to_int = *numeric_cast<int>(to_constant_expr(simpl_actual));
        REQUIRE(to_int == 5);
      }
    }

    WHEN("arg = serialized(true)")
    {
      const array_string_exprt arg = from_char_vector(
        {0, 0, 0, 1}, char_type, length_type, pointer_type, array_pool);
      format_specifiert fs{0, "", 0, 0, false, format_specifiert::BOOLEAN};
      const exprt actual =
        length_for_format_specifier(fs, arg, length_type, array_pool);
      const exprt simpl_actual = simplify_expr(actual, ns);
      THEN("length constraint represents 4")
      {
        const int to_int = *numeric_cast<int>(to_constant_expr(simpl_actual));
        REQUIRE(to_int == 4);
      }
    }

    WHEN("arg = serialized(null)")
    {
      const array_string_exprt arg = from_char_vector(
        {'n', 'u', 'l', 'l'}, char_type, length_type, pointer_type, array_pool);
      format_specifiert fs{0, "", 0, 0, false, format_specifiert::BOOLEAN};
      const exprt actual =
        length_for_format_specifier(fs, arg, length_type, array_pool);
      const exprt simpl_actual = simplify_expr(actual, ns);
      THEN(
        "length constraint represents 5 (because it should 'false', not 'null'")
      {
        const int to_int = *numeric_cast<int>(to_constant_expr(simpl_actual));
        REQUIRE(to_int == 5);
      }
    }
  }
}
