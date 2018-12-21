/*******************************************************************\

   Module: Unit tests for symex_target_equation::validate

   Author: Diffblue Ltd.

 \*******************************************************************/

#include <goto-symex/symex_target_equation.h>
#include <testing-utils/catch.hpp>
#include <util/arith_tools.h>

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

    symex_target_equationt equation;
    equation.SSA_steps.push_back(symex_target_equationt::SSA_stept());
    auto &step = equation.SSA_steps.back();
    step.type = goto_trace_stept::typet::FUNCTION_RETURN;
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
