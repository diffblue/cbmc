/*******************************************************************\

  Module: Unit tests for goto_program::validate

  Author: Diffblue Ltd.

 \*******************************************************************/

#include <goto-programs/goto_function.h>
#include <testing-utils/catch.hpp>
#include <util/arith_tools.h>

SCENARIO(
  "Validation of well-formed assert/assume codes",
  "[core][goto-programs][validate]")
{
  GIVEN("A program with one assumption")
  {
    symbol_tablet symbol_table;
    const typet type1 = signedbv_typet(32);
    symbolt symbol;
    symbolt fun_symbol;
    irep_idt fun_name = "foo";
    fun_symbol.name = fun_name;
    irep_idt symbol_name = "a";
    symbol.name = symbol_name;
    symbol_exprt varx(symbol_name, type1);
    exprt val10 = from_integer(10, type1);
    binary_relation_exprt x_le_10(varx, ID_le, val10);

    goto_functiont goto_function;
    auto &instructions = goto_function.body.instructions;
    instructions.emplace_back(goto_program_instruction_typet::ASSUME);

    symbol.type = type1;
    symbol_table.insert(symbol);
    symbol_table.insert(fun_symbol);
    namespacet ns(symbol_table);
    instructions.back().make_assertion(x_le_10);
    instructions.back().function = fun_name;

    WHEN("Instruction has no targets")
    {
      THEN("The consistency check succeeds")
      {
        goto_function.body.validate(ns, validation_modet::INVARIANT);
        REQUIRE(true);
      }
    }

    WHEN("Instruction has a target")
    {
      instructions.back().targets.push_back(instructions.begin());
      THEN("The consistency check fails")
      {
        REQUIRE_THROWS_AS(
          goto_function.body.validate(ns, validation_modet::EXCEPTION),
          incorrect_goto_program_exceptiont);
      }
    }
  }
}
