/*******************************************************************\

Module: Unit tests for remove_returns

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <goto-programs/remove_returns.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

TEST_CASE("Return-value removal", "[core][goto-programs][remove_returns]")
{
  symbol_tablet symbol_table;
  symbolt function_symbol;
  function_symbol.name = "a";
  function_symbol.pretty_name = "a";
  function_symbol.base_name = "a";
  function_symbol.type = code_typet({}, signedbv_typet(32));

  symbol_table.add(function_symbol);

  namespacet ns(symbol_table);

  symbol_exprt a_rv_symbol = return_value_symbol("a", ns);
  REQUIRE(is_return_value_symbol(a_rv_symbol));
  REQUIRE(is_return_value_identifier(a_rv_symbol.get_identifier()));

  irep_idt a_rv_id = return_value_identifier("a");

  REQUIRE(is_return_value_identifier(a_rv_id));

  symbol_exprt other_symbol("a::local", signedbv_typet(8));
  REQUIRE(!is_return_value_symbol(other_symbol));
  REQUIRE(!is_return_value_identifier(other_symbol.get_identifier()));
}
