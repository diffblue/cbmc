/*******************************************************************\

Module: Unit test for constant propagation

Author: Diffblue Ltd

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/message.h>

#include <analyses/constant_propagator.h>

#include <ansi-c/ansi_c_language.h>

#include <goto-programs/goto_convert_functions.h>

static bool starts_with_x(const exprt &e, const namespacet &)
{
  if(e.id() != ID_symbol)
    return false;
  return has_prefix(id2string(to_symbol_expr(e).get_identifier()), "x");
}

SCENARIO("constant_propagator", "[core][analyses][constant_propagator]")
{
  GIVEN("A simple GOTO program")
  {
    goto_modelt goto_model;
    namespacet ns(goto_model.symbol_table);

    // Create the program:
    // int x = 1;
    // int y = 2;

    symbolt local_x;
    symbolt local_y;
    local_x.name = "x";
    local_x.type = integer_typet();
    local_x.mode = ID_C;
    local_y.name = "y";
    local_y.type = integer_typet();
    local_y.mode = ID_C;

    code_blockt code;
    code.copy_to_operands(code_declt(local_x.symbol_expr()));
    code.copy_to_operands(code_declt(local_y.symbol_expr()));
    code.copy_to_operands(
      code_assignt(
        local_x.symbol_expr(), constant_exprt("1", integer_typet())));
    code.copy_to_operands(
      code_assignt(
        local_y.symbol_expr(), constant_exprt("2", integer_typet())));

    symbolt main_function_symbol;
    main_function_symbol.name = "main";
    main_function_symbol.type = code_typet();
    main_function_symbol.value = code;
    main_function_symbol.mode = ID_C;

    goto_model.symbol_table.add(local_x);
    goto_model.symbol_table.add(local_y);
    goto_model.symbol_table.add(main_function_symbol);

    goto_convert(goto_model, null_message_handler);

    const goto_functiont &main_function = goto_model.get_goto_function("main");

    // Find the instruction after "y = 2;"
    goto_programt::const_targett test_instruction =
      main_function.body.instructions.begin();
    while(
      test_instruction != main_function.body.instructions.end() &&
      (!test_instruction->is_assign() ||
       to_code_assign(test_instruction->code).lhs() != local_y.symbol_expr()))
    {
      ++test_instruction;
    }

    REQUIRE(test_instruction != main_function.body.instructions.end());
    ++test_instruction;

    WHEN("We apply conventional constant propagation")
    {
      constant_propagator_ait constant_propagator(main_function);
      constant_propagator(main_function_symbol.name, main_function, ns);

      THEN("The propagator should discover values for both 'x' and 'y'")
      {
        const auto &final_domain = constant_propagator[test_instruction];

        REQUIRE(final_domain.values.is_constant(local_x.symbol_expr()));
        REQUIRE(final_domain.values.is_constant(local_y.symbol_expr()));
      }
    }

    WHEN("We apply constant propagation for symbols beginning with 'x'")
    {
      constant_propagator_ait constant_propagator(main_function, starts_with_x);
      constant_propagator(main_function_symbol.name, main_function, ns);

      THEN("The propagator should discover a value for 'x' but not 'y'")
      {
        const auto &final_domain = constant_propagator[test_instruction];

        REQUIRE(final_domain.values.is_constant(local_x.symbol_expr()));
        REQUIRE(!final_domain.values.is_constant(local_y.symbol_expr()));
      }
    }
  }
}
