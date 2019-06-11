/*******************************************************************\

Module: Unit tests for length_of_decimal_int in
        solvers/refinement/string_format_builtin_function.cpp

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <solvers/strings/string_format_builtin_function.h>
#include <util/simplify_expr.h>
#include <util/symbol_table.h>

SCENARIO(
  "length_of_decimal_int",
  "[core][solvers][strings][string_format_builtin_function]")
{
  const typet type = signedbv_typet(32);

  const symbol_tablet symbol_table;
  const namespacet ns{symbol_table};

  const std::vector<mp_integer> input_values = {
    0, 1, 10, 15, 999, 1000000001, -1, -21111111, -1234567890};
  const std::vector<int> oracles_for_base_10 = {1, 1, 2, 2, 3, 10, 2, 9, 11};
  const std::vector<int> oracles_for_base_16 = {1, 1, 1, 1, 3, 8, 2, 8, 9};

  WHEN("base = 10")
  {
    for(size_t i = 0; i < input_values.size(); i++)
    {
      exprt input_expr = from_integer(input_values[i], type);
      WHEN("input exprt = " << input_values[i])
      {
        const exprt actual = length_of_decimal_int(input_expr, type, 10);
        const int oracle = oracles_for_base_10[i];
        THEN("length expression is " << oracle)
        {
          const int actual_int =
            numeric_cast<int>(to_constant_expr(simplify_expr(actual, ns)))
              .value();
          REQUIRE(actual_int == oracle);
        }
      }
    }
  }

  WHEN("base = 16")
  {
    for(size_t i = 0; i < input_values.size(); i++)
    {
      exprt input_expr = from_integer(input_values[i], type);
      WHEN("input exprt = " << input_values[i])
      {
        const exprt actual = length_of_decimal_int(input_expr, type, 16);
        const int oracle = oracles_for_base_16[i];
        THEN("length expression is " << oracle)
        {
          const int actual_int =
            *numeric_cast<int>(to_constant_expr(simplify_expr(actual, ns)));
          REQUIRE(actual_int == oracle);
        }
      }
    }
  }
}
