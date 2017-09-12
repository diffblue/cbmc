/*******************************************************************\

 Module: Unit tests for concretize_array_expression in
   solvers/refinement/string_refinement.cpp

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <catch.hpp>

#include <util/arith_tools.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <solvers/refinement/string_refinement.h>

SCENARIO("concretize_array_expression",
  "[core][solvers][refinement][string_refinement]")
{
  const typet char_type=unsignedbv_typet(16);
  const typet int_type=signedbv_typet(32);
  const exprt index1=from_integer(1, int_type);
  const exprt charx=from_integer('x', char_type);
  const exprt index4=from_integer(4, int_type);
  const exprt chary=from_integer('y', char_type);
  const exprt index100=from_integer(100, int_type);
  const exprt char0=from_integer('0', char_type);
  const exprt index2=from_integer(2, int_type);
  array_typet array_type(char_type, infinity_exprt(int_type));

  // input_expr is
  // `'0' + (ARRAY_OF(0) WITH [1:=x] WITH [4:=y] WITH [100:=z])[2]`
  const plus_exprt input_expr(
    from_integer('0', char_type),
    index_exprt(
      with_exprt(
        with_exprt(
          with_exprt(
            array_of_exprt(from_integer(0, char_type), array_type),
            index1,
            charx),
          index4,
          chary),
        index100,
        from_integer('z', char_type)),
      index2));

  // String max length is 50, so index 100 should get ignored.
  const exprt concrete=concretize_arrays_in_expression(input_expr, 50);

  // The expected result is `'0' + { 'x', 'x', 'y', 'y', 'y' }`
  array_exprt array(array_type);
  array.operands()={charx, charx, chary, chary, chary};
  const plus_exprt expected(char0, index_exprt(array, index2));
  REQUIRE(concrete==expected);
}
