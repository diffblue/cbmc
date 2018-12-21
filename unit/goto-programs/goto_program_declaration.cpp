/*******************************************************************\

Module: Unit tests for goto_program::validate

Author: Diffblue Ltd.

\*******************************************************************/

#include <goto-programs/goto_function.h>
#include <testing-utils/catch.hpp>
#include <util/arith_tools.h>

SCENARIO(
  "Validation of well-formed declaration codes",
  "[core][goto-programs][validate]")
{
  GIVEN("A program with one declaration")
  {
    symbol_tablet symbol_table;
    const signedbv_typet type1(32);

    symbolt fun_symbol;
    irep_idt fun_name = "foo";
    fun_symbol.name = fun_name;

    symbolt var_symbol;
    irep_idt var_symbol_name = "a";
    var_symbol.type = type1;
    var_symbol.name = var_symbol_name;
    symbol_exprt var_a(var_symbol_name, type1);

    goto_functiont goto_function;
    auto &instructions = goto_function.body.instructions;
    instructions.emplace_back(goto_program_instruction_typet::DECL);
    code_declt declaration(var_a);
    instructions.back().make_decl(declaration);
    instructions.back().function = fun_name;
    symbol_table.insert(fun_symbol);

    WHEN("Declaring known symbol")
    {
      symbol_table.insert(var_symbol);
      const namespacet ns(symbol_table);

      THEN("The consistency check succeeds")
      {
        goto_function.body.validate(ns, validation_modet::INVARIANT);
        REQUIRE(true);
      }
    }

    WHEN("Declaring unknown symbol")
    {
      const namespacet ns(symbol_table);

      THEN("The consistency check fails")
      {
        REQUIRE_THROWS_AS(
          goto_function.body.validate(ns, validation_modet::EXCEPTION),
          incorrect_goto_program_exceptiont);
      }
    }
  }
}
