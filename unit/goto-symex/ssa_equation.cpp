/*******************************************************************\

Module: Unit tests for symex_target_equation::validate

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>

#include <goto-symex/symex_target_equation.h>

SCENARIO("Validation of well-formed SSA steps", "[core][goto-symex][validate]")
{
  GIVEN("A program with one function return")
  {
    symbol_tablet symbol_table;
    const typet type1 = signedbv_typet(32);
    const code_typet code_type({}, type1);

    symbolt fun_symbol;
    irep_idt fun_name = "foo";
    fun_symbol.name = fun_name;
    symbol_exprt fun_foo(fun_name, code_type);

    goto_programt goto_program;
    goto_program.add_instruction(END_FUNCTION);
    symex_target_equationt equation(null_message_handler);
    symex_targett::sourcet at_end_function(fun_name, goto_program);
    equation.SSA_steps.emplace_back(
      at_end_function, goto_trace_stept::typet::FUNCTION_RETURN);
    auto &step = equation.SSA_steps.back();
    step.called_function = fun_name;

    WHEN("Called function is in symbol table")
    {
      symbol_table.insert(fun_symbol);
      namespacet ns(symbol_table);

      THEN("The consistency check succeeds")
      {
        REQUIRE_NOTHROW(equation.validate(ns, validation_modet::INVARIANT));
      }
    }

    WHEN("Called function is not in symbol table")
    {
      namespacet ns(symbol_table);

      THEN("The consistency check fails")
      {
        REQUIRE_THROWS_AS(
          equation.validate(ns, validation_modet::EXCEPTION),
          incorrect_goto_program_exceptiont);
      }
    }
  }
}
