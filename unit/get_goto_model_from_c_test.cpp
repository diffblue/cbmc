/*******************************************************************\

Module: Get goto model test

Author: Daniel Poetzl

\*******************************************************************/

#include <testing-utils/get_goto_model_from_c.h>
#include <testing-utils/use_catch.h>

TEST_CASE("Get goto model from C test", "[core]")
{
  const std::string code =
    "int g;"
    "void f(int a) { int b; }"
    "void main() {}";

  const auto goto_model = get_goto_model_from_c(code);

  const auto &function_map = goto_model.goto_functions.function_map;

  REQUIRE(function_map.find("main") != function_map.end());
  REQUIRE(function_map.find(CPROVER_PREFIX "_start") != function_map.end());
  REQUIRE(function_map.find("f") != function_map.end());

  const auto &main_instructions = function_map.at("main").body.instructions;
  REQUIRE(!main_instructions.empty());

  const auto &f_instructions = function_map.at("f").body.instructions;
  REQUIRE(f_instructions.size() >= 2);

  const auto &symbol_table = goto_model.symbol_table;

  REQUIRE(symbol_table.has_symbol("main"));
  REQUIRE(symbol_table.has_symbol(CPROVER_PREFIX "_start"));
  REQUIRE(symbol_table.has_symbol("g"));
  REQUIRE(symbol_table.has_symbol("f::a"));
  REQUIRE(symbol_table.has_symbol("f::1::b"));
}
