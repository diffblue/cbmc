/*******************************************************************\

 Module: Unit tests for goto_program::validate

 Author: Diffblue Ltd.

\*******************************************************************/

#include <goto-programs/goto_function.h>
#include <testing-utils/catch.hpp>
#include <util/arith_tools.h>

SCENARIO(
  "Validation of consistent program/table pair (type-wise)",
  "[core][goto-programs][validate]")
{
  GIVEN("A program with one assertion")
  {
    symbol_tablet symbol_table;
    const typet type1 = signedbv_typet(32);
    const typet type2 = signedbv_typet(64);
    symbolt symbol;
    irep_idt symbol_name = "a";
    symbol.name = symbol_name;
    symbol_exprt varx(symbol_name, type1);
    symbolt function_symbol;
    irep_idt function_name = "fun";
    function_symbol.name = function_name;

    exprt val10 = from_integer(10, type1);
    binary_relation_exprt x_le_10(varx, ID_le, val10);

    goto_functiont goto_function;
    auto &instructions = goto_function.body.instructions;
    instructions.emplace_back(goto_program_instruction_typet::ASSERT);
    instructions.back().make_assertion(x_le_10);
    instructions.back().function = function_symbol.name;

    symbol_table.insert(function_symbol);
    WHEN("Symbol table has the right symbol type")
    {
      symbol.type = type1;
      symbol_table.insert(symbol);
      const namespacet ns(symbol_table);

      THEN("The consistency check succeeds")
      {
        goto_function.validate(ns, validation_modet::INVARIANT);

        REQUIRE(true);
      }
    }

    WHEN("Symbol table has the wrong symbol type")
    {
      symbol.type = type2;
      symbol_table.insert(symbol);
      const namespacet ns(symbol_table);

      THEN("The consistency check fails")
      {
        REQUIRE_THROWS_AS(
          goto_function.validate(ns, validation_modet::EXCEPTION),
          incorrect_goto_program_exceptiont);
      }
    }
  }
}
