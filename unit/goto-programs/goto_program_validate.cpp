/*******************************************************************\
 Module: Unit tests for goto_program::validate

 Author: Diffblue Ltd.

 Date: Oct 2018

\*******************************************************************/

/// \file
/// Unit tests for goto program validation

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cmdline.h>
#include <util/config.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/validate_goto_model.h>

#include <ansi-c/goto-conversion/goto_convert_functions.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

SCENARIO("Validation of a goto program", "[core][goto-programs][validate]")
{
  // This test does require a proper architecture to be set so that C type
  // widths are configured.
  cmdlinet cmdline;
  config.set(cmdline);

  goto_modelt goto_model;

  // void f(){int x = 1;}
  symbolt x{"x", signed_int_type(), ID_C};
  goto_model.symbol_table.add(x);

  // void rtn, take no params
  symbolt f{"f", code_typet({}, empty_typet()), ID_C};
  code_blockt f_body{
    {code_declt(x.symbol_expr()),
     code_assignt(x.symbol_expr(), from_integer(1, signed_int_type()))}};
  f.value = f_body;
  goto_model.symbol_table.add(f);

  // void g(){int y = 2;}
  symbolt y{"y", signed_int_type(), ID_C};
  goto_model.symbol_table.add(y);

  symbolt g{"g", code_typet({}, empty_typet()), ID_C};
  code_blockt g_body{
    {code_declt{y.symbol_expr()},
     code_assignt{y.symbol_expr(), from_integer(2, signed_int_type())}}};
  g.value = g_body;
  goto_model.symbol_table.add(g);

  symbolt z{"z", signed_int_type(), ID_C};
  goto_model.symbol_table.add(z);

  // pointer to fn call
  symbolt fn_ptr{"fn_ptr", pointer_type(code_typet{{}, empty_typet()}), ID_C};
  goto_model.symbol_table.add(fn_ptr);

  symbolt entry_point{
    goto_functionst::entry_point(), code_typet({}, empty_typet{}), ID_C};
  code_blockt entry_point_body{
    {code_declt{z.symbol_expr()},
     code_assignt{z.symbol_expr(), from_integer(3, signed_int_type())},
     code_assignt{fn_ptr.symbol_expr(), address_of_exprt{f.symbol_expr()}},
     code_function_callt{g.symbol_expr()}}};

  entry_point.value = entry_point_body;
  goto_model.symbol_table.add(entry_point);

  /// check entry_point_exists()
  WHEN("the goto program has no entry point")
  {
    goto_convert(goto_model, null_message_handler);

    auto &function_map = goto_model.goto_functions.function_map;
    auto it = function_map.find(goto_functionst::entry_point());
    function_map.erase(it);

    THEN("fail!")
    {
      goto_model_validation_optionst validation_options{
        goto_model_validation_optionst ::set_optionst::all_false};
      validation_options.entry_point_exists = true;

      REQUIRE_THROWS_AS(
        validate_goto_model(
          goto_model.goto_functions,
          validation_modet::EXCEPTION,
          validation_options),
        incorrect_goto_program_exceptiont);
    }
  }

  WHEN("the goto program has an entry point")
  {
    goto_convert(goto_model, null_message_handler);
    THEN("pass!")
    {
      goto_model_validation_optionst validation_options{
        goto_model_validation_optionst ::set_optionst::all_false};

      validation_options.entry_point_exists = true;

      REQUIRE_NOTHROW(validate_goto_model(
        goto_model.goto_functions,
        validation_modet::EXCEPTION,
        validation_options));
    }
  }

  WHEN("all returns have been removed")
  {
    THEN("true!")
    {
      goto_convert(goto_model, null_message_handler);

      goto_model_validation_optionst validation_options{
        goto_model_validation_optionst ::set_optionst::all_false};

      validation_options.check_returns_removed = true;

      REQUIRE_NOTHROW(validate_goto_model(
        goto_model.goto_functions,
        validation_modet::EXCEPTION,
        validation_options));
    }
  }

  /// check_called_functions()
  WHEN("not every function call is in the function map")
  {
    THEN("fail!")
    {
      goto_convert(goto_model, null_message_handler);

      auto &function_map = goto_model.goto_functions.function_map;
      // the entry point has a call to g()
      auto it = function_map.find("g");
      function_map.erase(it);

      goto_model_validation_optionst validation_options{
        goto_model_validation_optionst ::set_optionst::all_false};

      REQUIRE_THROWS_AS(
        validate_goto_model(
          goto_model.goto_functions,
          validation_modet::EXCEPTION,
          validation_options),
        incorrect_goto_program_exceptiont);
    }
  }

  WHEN("not every function whose address is taken is in the function map")
  {
    THEN("fail!")
    {
      goto_convert(goto_model, null_message_handler);
      // the address of f is taken in the entry point function
      auto &function_map = goto_model.goto_functions.function_map;
      auto it = function_map.find("f");
      function_map.erase(it); // f is no longer in function map

      goto_model_validation_optionst validation_options{
        goto_model_validation_optionst ::set_optionst::all_false};

      REQUIRE_THROWS_AS(
        validate_goto_model(
          goto_model.goto_functions,
          validation_modet::EXCEPTION,
          validation_options),
        incorrect_goto_program_exceptiont);
    }
  }

  WHEN(
    "all functions calls and that of every function whose address is "
    "taken are in the function map")
  {
    THEN("true!")
    {
      goto_convert(goto_model, null_message_handler);

      goto_model_validation_optionst validation_options{
        goto_model_validation_optionst ::set_optionst::all_false};

      REQUIRE_NOTHROW(validate_goto_model(
        goto_model.goto_functions,
        validation_modet::EXCEPTION,
        validation_options));
    }
  }

  /// check_last_instruction()
  WHEN("the last instruction of a function is not an end function")
  {
    THEN("fail!")
    {
      goto_convert(goto_model, null_message_handler);
      auto &function_f = goto_model.goto_functions.function_map["f"];
      function_f.body.instructions.erase(
        std::prev(function_f.body.instructions.end()));

      namespacet ns(goto_model.symbol_table);

      REQUIRE_THROWS_AS(
        function_f.validate(ns, validation_modet::EXCEPTION),
        incorrect_goto_program_exceptiont);
    }
  }

  WHEN("the last instruction of a function is always an end function")
  {
    THEN("pass!")
    {
      goto_convert(goto_model, null_message_handler);
      auto &function_f = goto_model.goto_functions.function_map["f"];

      namespacet ns(goto_model.symbol_table);

      REQUIRE_NOTHROW(function_f.validate(ns, validation_modet::EXCEPTION));
    }
  }
}
