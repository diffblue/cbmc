/*******************************************************************\
 Module: Unit tests for goto_program::validate

 Author: Diffblue Ltd.

\*******************************************************************/

#include <goto-programs/goto_function.h>
#include <goto-programs/validate_goto_model.h>
#include <testing-utils/use_catch.h>
#include <util/arith_tools.h>

#include <util/c_types.h>
#include <util/std_code.h>

SCENARIO(
  "Validation of well-formed instruction",
  "[core][goto-programs][validate]")
{
  GIVEN("A function with one instruction")
  {
    symbol_tablet symbol_table;
    symbolt fun_symbol;
    irep_idt fun_name = "foo";
    fun_symbol.name = fun_name;

    goto_functiont goto_function;
    auto &instructions = goto_function.body.instructions;

    goto_programt::instructiont instruction;
    instruction.make_end_function();
    instructions.push_back(instruction);
    instructions.back().source_location.id("id_any_valid_id");

    codet instruction_code_field;
    static_cast<exprt &>(instruction_code_field)
      .add_source_location()
      .id("id_any_valid_id");
    instructions.back().code = instruction_code_field;

    symbol_table.insert(fun_symbol);
    namespacet ns(symbol_table);

    WHEN("the source locations are set and identical")
    {
      goto_model_validation_optionst validation_options{
        goto_model_validation_optionst ::set_optionst::all_false};

      validation_options.check_source_location = true;

      THEN("The consistency check succeeds")
      {
        REQUIRE_NOTHROW(goto_function.body.validate(
          ns, validation_modet::EXCEPTION, validation_options));
      }
    }

    WHEN("the source location is not set")
    {
      instructions.back().source_location.make_nil();

      goto_model_validation_optionst validation_options{
        goto_model_validation_optionst ::set_optionst::all_false};

      validation_options.check_source_location = true;

      THEN("The consistency check fails")
      {
        REQUIRE_THROWS_AS(
          goto_function.body.validate(
            ns, validation_modet::EXCEPTION, validation_options),
          incorrect_goto_program_exceptiont);
      }
    }

    WHEN("the 'code' source location is not set")
    {
      auto &expr = static_cast<exprt &>(instructions.back().code);
      expr.add_source_location().make_nil();

      goto_model_validation_optionst validation_options{
        goto_model_validation_optionst ::set_optionst::all_false};

      validation_options.check_source_location = true;

      THEN("The consistency check fails")
      {
        REQUIRE_THROWS_AS(
          goto_function.body.validate(
            ns, validation_modet::EXCEPTION, validation_options),
          incorrect_goto_program_exceptiont);
      }
    }

    WHEN("the source locations are not the same")
    {
      instructions.back().source_location.id("id_any_valid_id_1");

      auto &expr = static_cast<exprt &>(instructions.back().code);
      expr.add_source_location().id("id_any_valid_id_2");

      goto_model_validation_optionst validation_options{
        goto_model_validation_optionst ::set_optionst::all_false};

      validation_options.check_source_location = true;

      THEN("The consistency check fails")
      {
        REQUIRE_THROWS_AS(
          goto_function.body.validate(
            ns, validation_modet::EXCEPTION, validation_options),
          incorrect_goto_program_exceptiont);
      }
    }
  }
}
