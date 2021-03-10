/*******************************************************************\

 Module: Unit tests for `format` function.

 Author: DiffBlue Limited.

\*******************************************************************/

#include <util/bitvector_types.h>
#include <util/format.h>
#include <util/format_expr.h>
#include <util/std_code.h>

#include <testing-utils/use_catch.h>

TEST_CASE("Format a declaration statement.", "[core][util][format]")
{
  const signedbv_typet int_type{32};
  code_declt declaration{symbol_exprt{"foo", int_type}};
  REQUIRE(format_to_string(declaration) == "decl signedbv[32] foo;");
  declaration.set_initial_value({int_type.zero_expr()});
  REQUIRE(format_to_string(declaration) == "decl signedbv[32] foo = 0;");
}
