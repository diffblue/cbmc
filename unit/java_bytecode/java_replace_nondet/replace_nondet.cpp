/*******************************************************************\

 Module: Tests for the replace nondet pass to make sure it works both
         when remove_returns has been run before and after the call.

 Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/remove_returns.h>

#include <java_bytecode/remove_instanceof.h>
#include <java_bytecode/replace_java_nondet.h>

#include <util/config.h>
#include <util/options.h>

#include <goto-instrument/cover.h>

#include <iostream>

void validate_method_removal(
  std::list<goto_programt::instructiont> instructions)
{
  bool method_removed = true, replacement_nondet_exists = false;

  // Quick loop to check that our method call has been replaced.
  for(const auto &inst : instructions)
  {
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

TEST_CASE(
  "Load class with a generated java nondet method call, run remove returns "
  "both before and after the nondet statements have been removed, check "
  "results are as expected.",
  "[core][java_bytecode][replace_nondet]")
{
  GIVEN("A class with a call to CProver.nondetWithoutNull()")
  {
    symbol_tablet raw_symbol_table = load_java_class(
      "Main", "./java_bytecode/java_replace_nondet", "Main.replaceNondet");

    journalling_symbol_tablet symbol_table =
      journalling_symbol_tablet::wrap(raw_symbol_table);

    null_message_handlert null_output;
    goto_functionst functions;
    goto_convert(symbol_table, functions, null_output);

    const std::string function_name = "java::Main.replaceNondet:()V";
    goto_functionst::goto_functiont &goto_function =
      functions.function_map.at(function_name);

    goto_model_functiont model_function(
      symbol_table, functions, function_name, goto_function);

    remove_instanceof(goto_function, symbol_table);

    remove_virtual_functions(model_function);

    WHEN("Remove returns is called before java nondet.")
    {
      remove_returns(model_function, [](const irep_idt &) { return false; });

      replace_java_nondet(functions);

      THEN("The nondet method call should have been removed.")
      {
        validate_method_removal(goto_function.body.instructions);
      }
    }

    WHEN("Remove returns is called after java nondet.")
    {
      replace_java_nondet(functions);

      remove_returns(model_function, [](const irep_idt &) { return false; });

      THEN("The nondet method call should have been removed.")
      {
        validate_method_removal(goto_function.body.instructions);
      }
    }
  }
}
