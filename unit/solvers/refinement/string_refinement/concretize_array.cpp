/*******************************************************************\

Module: Unit tests for interval_sparse_arrayt::concretize in
        solvers/refinement/string_refinement_util.cpp

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/arith_tools.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <solvers/refinement/string_refinement.h>

SCENARIO("concretize_array_expression",
  "[core][solvers][refinement][string_refinement]")
{
  // Arrange
  const typet char_type=unsignedbv_typet(16);
  const typet int_type=signedbv_typet(32);
  const exprt index1=from_integer(1, int_type);
  const exprt charx=from_integer('x', char_type);
  const exprt index4=from_integer(4, int_type);
  const exprt chary=from_integer('y', char_type);
  const exprt index100=from_integer(100, int_type);
  const exprt char0=from_integer('0', char_type);
  const exprt index2=from_integer(2, int_type);
  const exprt charz = from_integer('z', char_type);
  array_typet array_type(char_type, infinity_exprt(int_type));

  // input_expr is
  // ARRAY_OF(0) WITH [1:=x] WITH [4:=y] WITH [100:=z]`
  const with_exprt input_expr(
    with_exprt(
      with_exprt(
        array_of_exprt(from_integer(0, char_type), array_type), index1, charx),
      index4,
      chary),
    index100,
    charz);

  // Act
  const interval_sparse_arrayt sparse_array(input_expr);
  // String size is 7, so index 100 should get ignored.
  const exprt concrete = sparse_array.concretize(7, int_type);

  // Assert
  // The expected result is `{ 'x', 'x', 'y', 'y', 'y', 'z', 'z' }`
  array_exprt expected(
    {charx, charx, chary, chary, chary, charz, charz}, array_type);
  to_array_type(expected.type()).size() = from_integer(7, int_type);
  REQUIRE(concrete==expected);
}
