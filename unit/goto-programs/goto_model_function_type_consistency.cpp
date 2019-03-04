/*******************************************************************\

Module: Unit tests for goto_model::validate

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/validate_goto_model.h>

SCENARIO(
  "Validation of consistent program/table pair (function type)",
  "[core][goto-programs][validate]")
{
  GIVEN("A model with one function")
  {
    const typet type1 = signedbv_typet(32);
    const typet type2 = signedbv_typet(64);
    code_typet fun_type1({}, type1);
    code_typet fun_type2({}, type2);

    symbolt function_symbol;
    function_symbol.mode = "C";
    irep_idt function_symbol_name = "foo";
    function_symbol.name = function_symbol_name;

    goto_modelt goto_model;
    goto_model.goto_functions.function_map[function_symbol.name] =
      goto_functiont();
    goto_model.goto_functions.function_map[function_symbol.name].type =
      fun_type1;

    goto_model_validation_optionst validation_options{
      goto_model_validation_optionst::set_optionst::all_false};

    WHEN("Symbol table has the right type")
    {
      function_symbol.type = fun_type1;
      goto_model.symbol_table.insert(function_symbol);

      THEN("The consistency check succeeds")
      {
        goto_model.validate(validation_modet::INVARIANT, validation_options);

        REQUIRE(true);
      }
    }

    WHEN("Symbol table has the wrong type")
    {
      function_symbol.type = fun_type2;
      goto_model.symbol_table.insert(function_symbol);

      THEN("The consistency check fails")
      {
        REQUIRE_THROWS_AS(
          goto_model.validate(validation_modet::EXCEPTION, validation_options),
          incorrect_goto_program_exceptiont);
      }
    }
  }
}
