/*******************************************************************\

Module: Unit tests for get_numeric_value_from_character in
        solvers/refinement/string_constraint_generator_valueof.cpp

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <iostream>
#include <solvers/strings/string_refinement.h>
#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/std_types.h>

SCENARIO("substitute_array_list", "[core][solvers][strings][string_refinement]")
{
  const typet char_type = unsignedbv_typet(16);
  const typet int_type = signedbv_typet(32);
  const array_typet array_type(char_type, infinity_exprt(int_type));
  const exprt index0 = from_integer(0, int_type);
  const exprt charx = from_integer('x', char_type);
  const exprt index1 = from_integer(1, int_type);
  const exprt chary = from_integer('y', char_type);
  const exprt index100 = from_integer(100, int_type);

  // arr is `array-list [ 0 , 'x' , 1 , 'y' , 2 , 'z']`
  array_list_exprt arr(
    {index0, charx, index1, chary, index100, from_integer('z', char_type)},
    array_type);

  // Max length is 2, so index 2 should get ignored.
  const exprt subst = substitute_array_lists(arr, 2);

  // Check that `subst = e1 WITH [1:='y']`
  REQUIRE(subst.id() == ID_with);
  REQUIRE(subst.operands().size() == 3);
  const exprt &e1 = to_with_expr(subst).old();
  REQUIRE(to_with_expr(subst).where() == index1);
  REQUIRE(to_with_expr(subst).new_value() == chary);

  // Check that `e1 = e2 WITH [0:='x']`
  REQUIRE(e1.id() == ID_with);
  REQUIRE(e1.operands().size() == 3);
  const exprt &e2 = to_with_expr(e1).old();
  REQUIRE(to_with_expr(e1).where() == index0);
  REQUIRE(to_with_expr(e1).new_value() == charx);

  // Check that `e1 = ARRAY_OF 0`
  REQUIRE(e2.id() == ID_array_of);
  REQUIRE(e2.operands().size() == 1);
  REQUIRE(to_array_of_expr(e2).op() == from_integer(0, char_type));
}
