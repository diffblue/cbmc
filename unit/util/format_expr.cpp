/*******************************************************************\

 Module: Unit tests for `format` function on expressions

 Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/format_expr.h>
#include <util/std_expr.h>

#include <testing-utils/use_catch.h>

TEST_CASE(
  "Format an expression with a format hook",
  "[core][util][format_hook]")
{
  irep_idt custom_id("custom_id");
  add_format_hook(
    custom_id, [](std::ostream &out, const exprt &expr) -> std::ostream & {
      out << "output";
      return out;
    });
  REQUIRE(format_to_string(exprt{custom_id}) == "output");
}

TEST_CASE("Format a bv-typed constant", "[core][util][format_expr]")
{
  auto value = make_bvrep(4, [](std::size_t index) { return index != 2; });
  auto expr = constant_exprt{value, bv_typet{4}};
  REQUIRE(format_to_string(expr) == "1011");
}
