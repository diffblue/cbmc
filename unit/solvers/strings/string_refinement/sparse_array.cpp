/*******************************************************************\

Module: Unit tests for sparse arrays in
        solvers/refinement/string_refinement.cpp

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <solvers/strings/string_refinement.h>

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#include <iostream>

SCENARIO("sparse_array", "[core][solvers][strings][string_refinement]")
{
  GIVEN("`ARRAY_OF(0) WITH [4:=x] WITH [1:=y] WITH [100:=z]`")
  {
    const typet char_type = unsignedbv_typet(16);
    const typet int_type = signedbv_typet(32);
    const exprt index1 = from_integer(1, int_type);
    const exprt charx = from_integer('x', char_type);
    const exprt index4 = from_integer(4, int_type);
    const exprt chary = from_integer('y', char_type);
    const exprt index100 = from_integer(100, int_type);
    const exprt char0 = from_integer('0', char_type);
    const exprt index2 = from_integer(2, int_type);
    const exprt charz = from_integer('z', char_type);
    const array_typet array_type(char_type, infinity_exprt(int_type));

    const with_exprt input_expr(
      with_exprt(
        with_exprt(
          array_of_exprt(from_integer(0, char_type), array_type),
          index4,
          charx),
        index1,
        chary),
      index100,
      charz);

    WHEN("It is converted to a sparse array")
    {
      THEN("The resulting if expression is index=100?z:index=4?x:index=1?y:0")
      {
        const symbol_exprt index("index", int_type);
        const if_exprt expected(
          equal_exprt(index, index100),
          charz,
          if_exprt(
            equal_exprt(index, index4),
            charx,
            if_exprt(
              equal_exprt(index, index1), chary, from_integer(0, char_type))));
        REQUIRE(sparse_arrayt::to_if_expression(input_expr, index) == expected);
      }
    }

    WHEN("It is converted to an interval sparse array")
    {
      const interval_sparse_arrayt sparse_array(input_expr);

      THEN(
        "The resulting if expression is index<=1?x:index<=4?y:index<=100?z:0")
      {
        const symbol_exprt index("index", int_type);
        const if_exprt expected(
          binary_relation_exprt(index, ID_le, index1),
          chary,
          if_exprt(
            binary_relation_exprt(index, ID_le, index4),
            charx,
            if_exprt(
              binary_relation_exprt(index, ID_le, index100),
              charz,
              from_integer(0, char_type))));
        REQUIRE(sparse_array.to_if_expression(index) == expected);
      }
    }
  }
}
