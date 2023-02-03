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
  "Validation of well-formed goto codes",
  "[core][goto-programs][validate]")
{
  GIVEN("A program with one assertion")
  {
    symbol_tablet symbol_table;
    const typet type1 = signedbv_typet(32);
    symbolt fun_symbol;
    irep_idt fun_name = "foo";
    fun_symbol.name = fun_name;

    symbolt symbol{"a", type1, irep_idt{}};
    symbol_exprt varx = symbol.symbol_expr();
    exprt val10 = from_integer(10, type1);
    binary_relation_exprt x_le_10(varx, ID_le, val10);

    goto_functiont goto_function;
    auto &instructions = goto_function.body.instructions;
    instructions.emplace_back(goto_programt::make_assertion(x_le_10));

    instructions.emplace_back(
      goto_programt::make_goto(instructions.begin(), true_exprt()));

    symbol_table.insert(symbol);
    symbol_table.insert(fun_symbol);
    namespacet ns(symbol_table);

    WHEN("Target is a target")
    {
      instructions.front().target_number = 1;
      THEN("The consistency check succeeds")
      {
        goto_function.body.validate(ns, validation_modet::INVARIANT);
        REQUIRE(true);
      }
    }

    WHEN("Target is not a target")
    {
      THEN("The consistency check fails")
      {
        REQUIRE_THROWS_AS(
          goto_function.body.validate(ns, validation_modet::EXCEPTION),
          incorrect_goto_program_exceptiont);
      }
    }
  }
}
