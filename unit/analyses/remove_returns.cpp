/*******************************************************************\
 Module: Unit tests for module remove_returns

 Author: Diffblue Ltd.

 Date: Apr 2019

\*******************************************************************/

/// \file
/// Unit tests for module remove_returns
/// This is testing the top level interfaces for now.

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/std_code.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/remove_returns.h>

// scenario for testing remove returns

SCENARIO(
  "Remove returns is working reliably",
  "[core][goto-programs][remove_returns]")
{
  goto_modelt goto_model;

  // int f() { return 5; }
  symbolt f;
  f.name = "f";
  f.mode = ID_C;
  f.type = code_typet{{}, signed_int_type()};
  f.value = code_blockt{{code_returnt(from_integer(5, signed_int_type()))}};
  goto_model.symbol_table.add(f);

  goto_convert(goto_model, null_message_handler);

  WHEN("remove_returns is invoked")
  {
    remove_returns(
      null_message_handler, goto_model.symbol_table, goto_model.goto_functions);
    THEN("function f should not contain any return instructions")
    {
      const auto &goto_functions = goto_model.goto_functions;
      for(const auto &function_pair : goto_functions.function_map)
      {
        if(function_pair.first == "f")
        {
          const auto &instructions = function_pair.second.body.instructions;
          for(auto target = instructions.begin(); target != instructions.end();
              target++)
          {
            // make sure there are no return instructions.
            REQUIRE(!target->is_return());
          }
        }
      }
    }
  }

  WHEN("restore_returns is invoked")
  {
    restore_returns(null_message_handler, goto_model);
    THEN("function f should have a skip instruction")
    {
      int number_of_returns = 0;
      const auto &goto_functions = goto_model.goto_functions;
      for(const auto &function_pair : goto_functions.function_map)
      {
        if(function_pair.first == "f")
        {
          const auto &instructions = function_pair.second.body.instructions;
          for(auto target = instructions.begin(); target != instructions.end();
              target++)
          {
            if(target->is_return())
              number_of_returns++;
          }
        }
      }

      // ensure that there were only 1 return instructions in f
      REQUIRE(number_of_returns == 1);
    }
  }
}

// scenario for testing restore returns
