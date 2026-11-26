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

/// Matches an incorrect_goto_program_exceptiont whose message contains
/// \p expected.
static auto exception_containing(const std::string &expected)
{
  return Catch::Matchers::Predicate<incorrect_goto_program_exceptiont>(
    [expected](const incorrect_goto_program_exceptiont &exception)
    { return exception.what().find(expected) != std::string::npos; },
    "incorrect_goto_program_exceptiont with a message containing \"" +
      expected + "\"");
}

/// The instructions of a body with two nested loops and a forward goto
struct nested_loops_bodyt
{
  goto_programt::targett outer_head;
  goto_programt::targett forward_goto;
  goto_programt::targett inner_head;
  goto_programt::targett inner_back_goto;
  goto_programt::targett outer_back_goto;
  goto_programt::targett end_function;
};

/// Adds to \p body, in this order, where c is a condition and the number of
/// each instruction after update() is its position:
///   SKIP              (outer loop head, target number 1)
///   GOTO end if c     (forward goto)
///   SKIP              (inner loop head, target number 2)
///   GOTO inner if c   (backward goto, loop number 0)
///   GOTO outer if c   (backward goto, loop number 1)
///   SKIP
///   END_FUNCTION      (target number 3)
static nested_loops_bodyt add_nested_loops_body(goto_programt &body)
{
  const symbol_exprt condition{"c", bool_typet{}};
  nested_loops_bodyt result;
  result.outer_head = body.add(goto_programt::make_skip());
  result.forward_goto =
    body.add(goto_programt::make_goto(body.instructions.end(), condition));
  result.inner_head = body.add(goto_programt::make_skip());
  result.inner_back_goto =
    body.add(goto_programt::make_goto(result.inner_head, condition));
  result.outer_back_goto =
    body.add(goto_programt::make_goto(result.outer_head, condition));
  body.add(goto_programt::make_skip());
  result.end_function = body.add(goto_programt::make_end_function());
  result.forward_goto->set_target(result.end_function);
  return result;
}

SCENARIO(
  "Validation of the numbering of a goto program",
  "[core][goto-programs][validate_numbering]")
{
  const validation_modet vm = validation_modet::EXCEPTION;

  GIVEN("an empty goto program")
  {
    const goto_programt body;
    THEN("its numbering is valid")
    {
      REQUIRE_NOTHROW(body.validate_numbering(vm));
    }
  }

  GIVEN("a goto program with nested loops and a forward goto, after update()")
  {
    goto_programt body;
    const nested_loops_bodyt instructions = add_nested_loops_body(body);
    body.update();

    THEN("its numbering is valid")
    {
      REQUIRE_NOTHROW(body.validate_numbering(vm));
    }

    WHEN("an instruction has the location number of the previous instruction")
    {
      instructions.forward_goto->location_number =
        instructions.outer_head->location_number;

      THEN("the location numbers are rejected")
      {
        REQUIRE_THROWS_MATCHES(
          body.validate_numbering(vm),
          incorrect_goto_program_exceptiont,
          exception_containing("location numbers must strictly increase"));
      }
    }

    WHEN("a jump target has no target number")
    {
      instructions.end_function->target_number =
        goto_programt::instructiont::nil_target;

      THEN("the target numbers are rejected")
      {
        REQUIRE_THROWS_MATCHES(
          body.validate_numbering(vm),
          incorrect_goto_program_exceptiont,
          exception_containing("a jump target must have a target number"));
      }
    }

    WHEN("an instruction that is no jump target has a target number")
    {
      instructions.forward_goto->target_number = 4;

      THEN("the target numbers are rejected")
      {
        REQUIRE_THROWS_MATCHES(
          body.validate_numbering(vm),
          incorrect_goto_program_exceptiont,
          exception_containing(
            "is not a jump target must not have a target number"));
      }
    }

    WHEN("two jump targets have their target numbers swapped")
    {
      instructions.outer_head->target_number = 2;
      instructions.inner_head->target_number = 1;

      THEN("the target numbers are rejected")
      {
        REQUIRE_THROWS_MATCHES(
          body.validate_numbering(vm),
          incorrect_goto_program_exceptiont,
          exception_containing("target numbers must be 1, 2, 3"));
      }
    }

    WHEN("two backward gotos have the same loop number")
    {
      instructions.outer_back_goto->loop_number = 0;

      THEN("the loop numbers are rejected")
      {
        REQUIRE_THROWS_MATCHES(
          body.validate_numbering(vm),
          incorrect_goto_program_exceptiont,
          exception_containing("loop numbers must be 0, 1, 2"));
      }
    }

    WHEN("an incoming edge is missing")
    {
      instructions.end_function->incoming_edges.erase(
        instructions.forward_goto);

      THEN("the incoming edges are rejected")
      {
        REQUIRE_THROWS_MATCHES(
          body.validate_numbering(vm),
          incorrect_goto_program_exceptiont,
          exception_containing("the incoming edges of an instruction"));
      }
    }

    WHEN("an incoming edge is from an instruction that is no predecessor")
    {
      instructions.inner_head->incoming_edges.insert(instructions.end_function);

      THEN("the incoming edges are rejected")
      {
        REQUIRE_THROWS_MATCHES(
          body.validate_numbering(vm),
          incorrect_goto_program_exceptiont,
          exception_containing("the incoming edges of an instruction"));
      }
    }

    WHEN(
      "an incoming edge is replaced by an instruction that is no predecessor")
    {
      // The number of incoming edges stays the same
      instructions.end_function->incoming_edges.erase(
        instructions.forward_goto);
      instructions.end_function->incoming_edges.insert(instructions.inner_head);

      THEN("the incoming edges are rejected")
      {
        REQUIRE_THROWS_MATCHES(
          body.validate_numbering(vm),
          incorrect_goto_program_exceptiont,
          exception_containing("the incoming edges of an instruction"));
      }
    }
  }
}

SCENARIO(
  "Validation of the numbering of goto functions",
  "[core][goto-programs][validate_numbering]")
{
  const validation_modet vm = validation_modet::EXCEPTION;

  GIVEN("two functions with a body and one without, after update()")
  {
    goto_functionst goto_functions;
    goto_programt &first = goto_functions.function_map["first_function"].body;
    goto_programt &second = goto_functions.function_map["second_function"].body;
    goto_functions.function_map["function_without_body"];
    const nested_loops_bodyt first_instructions = add_nested_loops_body(first);
    const nested_loops_bodyt second_instructions =
      add_nested_loops_body(second);
    goto_functions.update();

    THEN("the numbering is valid")
    {
      REQUIRE_NOTHROW(goto_functions.validate_numbering(vm));
    }

    WHEN("the numbering of a body is not valid")
    {
      second_instructions.outer_back_goto->loop_number = 0;

      THEN("the function is named with the reason")
      {
        REQUIRE_THROWS_MATCHES(
          goto_functions.validate_numbering(vm),
          incorrect_goto_program_exceptiont,
          exception_containing("second_function") &&
            exception_containing("loop numbers must be 0, 1, 2"));
      }
    }

    WHEN("a body is numbered alone, with the numbers of another body")
    {
      second.update();

      THEN("the ranges overlap and both functions are named")
      {
        REQUIRE_THROWS_MATCHES(
          goto_functions.validate_numbering(vm),
          incorrect_goto_program_exceptiont,
          exception_containing("overlap") &&
            exception_containing("first_function") &&
            exception_containing("second_function"));
      }
    }

    WHEN("the first location number of a body is the last one of another")
    {
      unsigned number = first_instructions.end_function->location_number;
      second.compute_location_numbers(number);

      THEN("the ranges overlap")
      {
        REQUIRE_THROWS_MATCHES(
          goto_functions.validate_numbering(vm),
          incorrect_goto_program_exceptiont,
          exception_containing("overlap"));
      }
    }

    WHEN("the last location number of a body is the unused location number")
    {
      // update() has numbered the 14 instructions with 0 to 13
      unsigned number = 8;
      second.compute_location_numbers(number);

      THEN("the unused location number is rejected")
      {
        REQUIRE_THROWS_MATCHES(
          goto_functions.validate_numbering(vm),
          incorrect_goto_program_exceptiont,
          exception_containing("second_function") &&
            exception_containing("unused location number"));
      }
    }
  }
}
