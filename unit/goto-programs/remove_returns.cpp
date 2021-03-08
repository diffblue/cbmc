/*******************************************************************\

Module: Unit tests for remove_returns

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/invariant.h>
#include <testing-utils/use_catch.h>

#include <goto-programs/goto_functions.h>
#include <goto-programs/remove_returns.h>

#include <util/bitvector_types.h>
#include <util/namespace.h>
#include <util/std_expr.h>
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

TEST_CASE(
  "remove_returns missing function invariant",
  "[core][goto-programs][remove_returns]")
{
  symbol_tablet symbol_table;
  goto_functionst goto_functions;

  symbolt foo_function_symbol;
  foo_function_symbol.name = "foo_function";
  foo_function_symbol.type = code_typet{{}, empty_typet{}};
  symbol_table.insert(foo_function_symbol);

  symbolt bar_function_symbol;
  bar_function_symbol.name = "bar_function";
  bar_function_symbol.type = code_typet{{}, signedbv_typet{32}};
  symbol_table.insert(bar_function_symbol);

  *goto_functions.function_map["foo_function"].body.add_instruction() =
    goto_programt::make_function_call(
      code_function_callt{symbol_exprt{"local_variable", signedbv_typet{32}},
                          bar_function_symbol.symbol_expr(),
                          {}});
  const cbmc_invariants_should_throwt invariants_throw;
  REQUIRE_THROWS_MATCHES(
    remove_returns(symbol_table, goto_functions),
    invariant_failedt,
    invariant_failure_containing("called function `bar_function' should have "
                                 "an entry in the function map"));
}
