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

    exprt val10 = from_integer(10, type1);
    binary_relation_exprt x_le_10(varx, ID_le, val10);

    goto_functiont goto_function;
    auto &instructions = goto_function.body.instructions;
    instructions.emplace_back(goto_program_instruction_typet::ASSERT);
    instructions.back().make_assertion(x_le_10);

    WHEN("Symbol table has the right symbol type")
    {
      symbol.type = type1;
      symbol_table.insert(symbol);

      THEN("The consistency check succeeds")
      {
        goto_function.validate(symbol_table, validation_modet::INVARIANT);

        REQUIRE(true);
      }
    }

    WHEN("Symbol table has the wrong symbol type")
    {
      symbol.type = type2;
      symbol_table.insert(symbol);

      THEN("The consistency check fails")
      {
        bool caught = false;
        try
        {
          goto_function.validate(symbol_table, validation_modet::EXCEPTION);
        }
        catch(incorrect_goto_program_exceptiont &e)
        {
          caught = true;
        }
        REQUIRE(caught);
      }
    }
  }
}
