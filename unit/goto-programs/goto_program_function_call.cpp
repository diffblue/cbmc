/*******************************************************************\

Module: Unit tests for goto_program::validate

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>

#include <goto-programs/goto_function.h>

SCENARIO(
  "Validation of well-formed function call codes",
  "[core][goto-programs][validate]")
{
  GIVEN("A program with one function call")
  {
    symbol_tablet symbol_table;
    const signedbv_typet type1(32);
    const signedbv_typet type2(64);
    const code_typet code_type({}, type1);

    symbolt var_symbol;
    irep_idt var_symbol_name = "a";
    var_symbol.name = var_symbol_name;
    symbol_exprt var_a(var_symbol_name, type1);

    symbolt var_symbol2;
    irep_idt var_symbol_name2 = "b";
    var_symbol2.name = var_symbol_name2;
    symbol_exprt var_b(var_symbol_name2, type2);

    symbolt fun_symbol;
    irep_idt fun_symbol_name = "foo";
    fun_symbol.name = fun_symbol_name;
    fun_symbol.type = code_type;
    symbol_exprt fun_foo(fun_symbol_name, code_type);

    goto_functiont goto_function;
    auto &instructions = goto_function.body.instructions;
    instructions.emplace_back(goto_program_instruction_typet::FUNCTION_CALL);
    instructions.back().function = fun_symbol_name;

    var_symbol.type = type1;
    var_symbol2.type = type2;
    symbol_table.insert(var_symbol);
    symbol_table.insert(var_symbol2);
    symbol_table.insert(fun_symbol);
    namespacet ns(symbol_table);

    WHEN("Return type matches")
    {
      code_function_callt function_call(var_a, fun_foo, {});
      instructions.back().make_function_call(function_call);
      REQUIRE(instructions.back().code.get_statement() == ID_function_call);

      THEN("The consistency check succeeds")
      {
        goto_function.body.validate(ns, validation_modet::INVARIANT);
        REQUIRE(true);
      }
    }

    WHEN("Return type differs from function type")
    {
      code_function_callt function_call(var_b, fun_foo, {});
      instructions.back().make_function_call(function_call);

      THEN("The consistency check fails")
      {
        REQUIRE_THROWS_AS(
          goto_function.body.validate(ns, validation_modet::EXCEPTION),
          incorrect_goto_program_exceptiont);
      }
    }
  }
}
