/*******************************************************************\

Module: Unit tests for goto_program::validate

Author: Diffblue Ltd.

\*******************************************************************/

#include <util/bitvector_types.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_function.h>

#include <testing-utils/use_catch.h>

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

    symbolt var_symbol{"a", type1, irep_idt{}};
    symbol_exprt var_a = var_symbol.symbol_expr();

    symbolt var_symbol2{"b", type2, irep_idt{}};
    symbol_exprt var_b = var_symbol2.symbol_expr();

    symbolt fun_symbol{"foo", code_type, irep_idt{}};
    symbol_exprt fun_foo = fun_symbol.symbol_expr();

    goto_functiont goto_function;
    auto &instructions = goto_function.body.instructions;
    instructions.emplace_back(goto_program_instruction_typet::FUNCTION_CALL);

    symbol_table.insert(var_symbol);
    symbol_table.insert(var_symbol2);
    symbol_table.insert(fun_symbol);
    namespacet ns(symbol_table);

    WHEN("Return type matches")
    {
      code_function_callt function_call(var_a, fun_foo, {});
      instructions.back() = goto_programt::make_function_call(function_call);
      REQUIRE(instructions.back().code().get_statement() == ID_function_call);

      THEN("The consistency check succeeds")
      {
        goto_function.body.validate(ns, validation_modet::INVARIANT);
        REQUIRE(true);
      }
    }

    WHEN("Return type differs from function type")
    {
      code_function_callt function_call(var_b, fun_foo, {});
      instructions.back() = goto_programt::make_function_call(function_call);

      THEN("The consistency check fails")
      {
        REQUIRE_THROWS_AS(
          goto_function.body.validate(ns, validation_modet::EXCEPTION),
          incorrect_goto_program_exceptiont);
      }
    }
  }
}
