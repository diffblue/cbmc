/*******************************************************************\

Module: Unit tests for goto_program::validate

Author: Diffblue Ltd.

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_function.h>

#include <testing-utils/use_catch.h>

SCENARIO(
  "Validation of well-formed assert/assume codes",
  "[core][goto-programs][validate]")
{
  GIVEN("A program with one assumption")
  {
    symbol_tablet symbol_table;
    const typet type1 = signedbv_typet(32);
    symbolt symbol{"a", type1, ID_C};
    irep_idt fun_name = "foo";
    symbolt fun_symbol;
    fun_symbol.name = fun_name;
    symbol_exprt varx = symbol.symbol_expr();
    exprt val10 = from_integer(10, type1);
    binary_relation_exprt x_le_10(varx, ID_le, val10);

    goto_functiont goto_function;
    auto assertion =
      goto_function.body.add(goto_programt::make_assertion(x_le_10));

    symbol_table.insert(symbol);
    symbol_table.insert(fun_symbol);
    namespacet ns(symbol_table);

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
      assertion->targets.push_back(assertion);
      THEN("The consistency check fails")
      {
        REQUIRE_THROWS_AS(
          goto_function.body.validate(ns, validation_modet::EXCEPTION),
          incorrect_goto_program_exceptiont);
      }
    }
  }
}
