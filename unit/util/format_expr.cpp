/*******************************************************************\

 Module: Unit tests for `format` function on expressions

 Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/expr.h>
#include <util/format_expr.h>

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
