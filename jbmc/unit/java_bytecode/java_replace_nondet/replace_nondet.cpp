/*******************************************************************\

 Module: Tests for the replace nondet pass to make sure it works both
         when remove_returns has been run before and after the call.

 Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <testing-utils/catch.hpp>
#include <testing-utils/message.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/remove_returns.h>

#include <java_bytecode/convert_java_nondet.h>
#include <java_bytecode/object_factory_parameters.h>
#include <java_bytecode/remove_instanceof.h>
#include <java_bytecode/replace_java_nondet.h>

#include <util/config.h>
#include <util/options.h>

#include <goto-instrument/cover.h>

#include <iostream>
#include <java-testing-utils/load_java_class.h>

void validate_nondet_method_removed(
  std::list<goto_programt::instructiont> instructions)
{
  bool method_removed = true, replacement_nondet_exists = false;

  // Loop over our instructions to make sure the nondet java method call has
  // been removed and that we can find an assignment/return with a nondet
  // as it's right-hand side.
  for(const auto &inst : instructions)
  {
    // Check that our NONDET(<type>) exists on a rhs somewhere.
    if(inst.is_assign())
    {
      const code_assignt &assignment = to_code_assign(inst.code);
      if(assignment.rhs().id() == ID_side_effect)
      {
        const side_effect_exprt &see = to_side_effect_expr(assignment.rhs());
        if(see.get_statement() == ID_nondet)
        {
          replacement_nondet_exists = true;
        }
      }
    }

    if(inst.is_return())
    {
      const code_returnt &ret_expr = to_code_return(inst.code);
      if(ret_expr.return_value().id() == ID_side_effect)
      {
        const side_effect_exprt &see =
          to_side_effect_expr(ret_expr.return_value());
        if(see.get_statement() == ID_nondet)
        {
          replacement_nondet_exists = true;
        }
      }
    }

    // And check to see that our nondet method call has been removed.
    if(inst.is_function_call())
    {
      const code_function_callt &function_call =
        to_code_function_call(inst.code);

      // Small check to make sure the instruction is a symbol.
      if(function_call.function().id() != ID_symbol)
        continue;

      const irep_idt function_id =
        to_symbol_expr(function_call.function()).get_identifier();
      if(
        function_id ==
        "java::org.cprover.CProver.nondetWithoutNull:()"
        "Ljava/lang/Object;")
      {
        method_removed = false;
      }
    }
  }

  REQUIRE(method_removed);
  REQUIRE(replacement_nondet_exists);
}

void validate_nondets_converted(
  std::list<goto_programt::instructiont> instructions)
{
  bool nondet_exists = false;
  bool allocate_exists = false;
  for(const auto &inst : instructions)
  {
    // Check that our NONDET(<type>) exists on a rhs somewhere.
    exprt target_expression =
      (inst.is_assign()
         ? to_code_assign(inst.code).rhs()
         : inst.is_return() ? to_code_return(inst.code).return_value()
                            : inst.code);

    if(
      const auto side_effect =
        expr_try_dynamic_cast<side_effect_exprt>(target_expression))
    {
      if(side_effect->get_statement() == ID_nondet)
      {
        nondet_exists = true;
      }

      if(side_effect->get_statement() == ID_allocate)
      {
        allocate_exists = true;
      }
    }
  }

  REQUIRE_FALSE(nondet_exists);
  REQUIRE(allocate_exists);
}

void load_and_test_method(
  const std::string &method_signature,
  goto_functionst &functions,
  journalling_symbol_tablet &symbol_table)
{
  // Find the method under test.
  const std::string function_name = "java::Main." + method_signature;
  goto_functionst::goto_functiont &goto_function =
    functions.function_map.at(function_name);

  goto_model_functiont model_function(
    symbol_table, functions, function_name, goto_function);

  // Emulate some of the passes that we'd normally do before replace_java_nondet
  // is called.
  remove_instanceof(goto_function, symbol_table, null_message_handler);

  remove_virtual_functions(model_function);

  // Then test both situations.
  THEN("Replace nondet should work after remove returns has been called.")
  {
    remove_returns(model_function, [](const irep_idt &) { return false; });

    replace_java_nondet(model_function);

    validate_nondet_method_removed(goto_function.body.instructions);
  }

  THEN("Replace nondet should work before remove returns has been called.")
  {
    replace_java_nondet(model_function);

    remove_returns(model_function, [](const irep_idt &) { return false; });

    validate_nondet_method_removed(goto_function.body.instructions);
  }

  object_factory_parameterst params{};

  THEN(
    "Replace and convert nondet should work after remove returns has been "
    "called.")
  {
    remove_returns(model_function, [](const irep_idt &) { return false; });

    replace_java_nondet(model_function);

    convert_nondet(model_function, null_message_handler, params, ID_java);

    validate_nondets_converted(goto_function.body.instructions);
  }

  THEN(
    "Replace and convert nondet should work before remove returns has been "
    "called.")
  {
    replace_java_nondet(model_function);

    convert_nondet(model_function, null_message_handler, params, ID_java);

    remove_returns(model_function, [](const irep_idt &) { return false; });

    validate_nondets_converted(goto_function.body.instructions);
  }
}

SCENARIO(
  "Testing replace_java_nondet correctly replaces CProver.nondet method calls.",
  "[core][java_bytecode][replace_nondet]")
{
  GIVEN("A class that holds nondet calls.")
  {
    // Load our main class.
    symbol_tablet raw_symbol_table =
      load_java_class("Main", "./java_bytecode/java_replace_nondet");

    journalling_symbol_tablet symbol_table =
      journalling_symbol_tablet::wrap(raw_symbol_table);

    // Convert bytecode into goto.
    goto_functionst functions;
    goto_convert(symbol_table, functions, null_message_handler);

    WHEN("A method assigns a local Object variable with nondetWithoutNull.")
    {
      load_and_test_method(
        "replaceNondetAssignment:()V", functions, symbol_table);
    }

    WHEN(
      "A method assigns an Integer variable with nondetWithoutNull. Causes "
      "implicit cast.")
    {
      load_and_test_method(
        "replaceNondetAssignmentImplicitCast:()V", functions, symbol_table);
    }

    WHEN(
      "A method assigns an Integer variable with nondetWithoutNull. Uses "
      "explicit cast.")
    {
      load_and_test_method(
        "replaceNondetAssignmentExplicitCast:()V", functions, symbol_table);
    }

    WHEN("A method directly returns a nonDetWithoutNull of type Object.")
    {
      load_and_test_method(
        "replaceNondetReturn:()Ljava/lang/Object;", functions, symbol_table);
    }

    WHEN(
      "A method directly returns a nonDetWithoutNull of type Integer. Causes "
      "implicit cast.")
    {
      load_and_test_method(
        "replaceNondetReturnWithImplicitCast:()Ljava/lang/Integer;",
        functions,
        symbol_table);
    }

    WHEN(
      "A method directly returns a nonDetWithoutNull of type Integer. Uses "
      "explicit cast.")
    {
      load_and_test_method(
        "replaceNondetReturnWithExplicitCast:()Ljava/lang/Integer;",
        functions,
        symbol_table);
    }

    // These currently cause an abort, issue detailed in https://github.com/diffblue/cbmc/issues/2281.

    //    WHEN(
    //      "A method directly returns a nonDetWithoutNull +3 with explicit int cast.")
    //    {
    //      load_and_test_method("replaceNondetReturnAddition:()Ljava/lang/Integer;", functions, symbol_table);
    //    }

    //    WHEN(
    //      "A method assigns an int variable with nondetWithoutNull. Causes "
    //      "unboxing.")
    //    {
    //      load_and_test_method("replaceNondetAssignmentUnbox:()V", functions, symbol_table);
    //    }

    //    WHEN(
    //      "A method assigns an int variable with nondetWithoutNull +3 with explicit cast.")
    //    {
    //      load_and_test_method("replaceNondetAssignmentAddition:()V", functions, symbol_table);
    //    }

    //    WHEN(
    //      "A method that calls nondetWithoutNull() without assigning the return value.")
    //    {
    //      load_and_test_method("replaceNondetUnused:()V", functions, symbol_table);
    //    }

    //    WHEN(
    //      "A method directly returns a nonDetWithoutNull of type int. Causes "
    //      "unboxing.")
    //    {
    //      load_and_test_method("replaceNondetReturnUnboxed:()I", functions, symbol_table);
    //    }
  }
}
