/*******************************************************************\

Module: Unit tests for goto_program::validate

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>

#include <goto-programs/goto_function.h>

SCENARIO(
  "Validation of consistent program/table pair",
  "[core][goto-programs][validate]")
{
  GIVEN("A program with one assertion")
  {
    symbol_tablet symbol_table;
    const typet type = signedbv_typet(32);
    symbolt symbol;
    irep_idt symbol_name = "a";
    symbol.name = symbol_name;
    symbol_exprt varx(symbol_name, type);
    symbolt function_symbol;
    irep_idt function_name = "fun";
    function_symbol.name = function_name;

    exprt val10 = from_integer(10, type);
    binary_relation_exprt x_le_10(varx, ID_le, val10);

    goto_functiont goto_function;
    auto &instructions = goto_function.body.instructions;
    instructions.emplace_back(goto_programt::make_assertion(x_le_10));

    // required as goto_function.validate checks (if a function has a body) that
    // the last instruction of a function body marks the function's end.
    goto_programt::instructiont end_function_instruction;
    end_function_instruction.make_end_function();
    instructions.push_back(end_function_instruction);

    symbol_table.insert(function_symbol);
    WHEN("Symbol table has the right symbol")
    {
      symbol.type = type;
      symbol_table.insert(symbol);
      const namespacet ns(symbol_table);
      THEN("The consistency check succeeds")
      {
        goto_function.validate(ns, validation_modet::INVARIANT);
        REQUIRE(true);
      }
    }
    WHEN("Symbol table does not have the symbol")
    {
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
