/*******************************************************************\

 Module: Unit tests for `format` function.

 Author: DiffBlue Limited.

\*******************************************************************/

#include <util/bitvector_types.h>
#include <util/format_expr.h>
#include <util/std_expr.h>

#include <testing-utils/use_catch.h>

TEST_CASE("Format an expression.", "[core][util][format]")
{
  const signedbv_typet int_type{32};
  plus_exprt plus{symbol_exprt{"foo", int_type}, symbol_exprt{"bar", int_type}};
  REQUIRE(format_to_string(plus) == "foo + bar");
}
