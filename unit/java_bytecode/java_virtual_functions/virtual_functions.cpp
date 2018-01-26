/*******************************************************************\

 Module: Unit tests for java_types

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>
#include <testing-utils/require_goto_statements.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_virtual_functions.h>
#include <util/config.h>

#include <util/std_expr.h>

void check_function_call(
  const equal_exprt &eq_expr,
  const irep_idt &class_name,
  const irep_idt &function_name,
  const goto_programt::targetst &targets)
{
  REQUIRE(eq_expr.op0().id() == ID_constant);
  REQUIRE(eq_expr.op0().type().id() == ID_string);
  REQUIRE(to_constant_expr(eq_expr.op0()).get_value() == class_name);

  REQUIRE(targets.size() == 1);

  for(const auto &target : targets)
  {
    REQUIRE(target->type == goto_program_instruction_typet::FUNCTION_CALL);
    const code_function_callt call = to_code_function_call(target->code);
    REQUIRE(call.function().id() == ID_symbol);
    REQUIRE(to_symbol_expr(call.function()).get_identifier() == function_name);
  }
}

SCENARIO(
  "load class with virtual method call, resolve to all valid calls",
  "[core][java_bytecode][virtual_functions]")
{
  config.set_arch("none");
  GIVEN("A class with a call to java.lang.Object.toString()")
  {
    const symbol_tablet &symbol_table =
      load_java_class("E", "./java_bytecode/java_virtual_functions", "E.f");

    const std::string function_name =
      "java::E.f:(Ljava/lang/Object;)Ljava/lang/String;";

    WHEN("The entry point function is generated")
    {
      symbol_tablet new_table(symbol_table);
      null_message_handlert null_output;
      goto_functionst new_goto_functions;
      goto_convert(new_table, new_goto_functions, null_output);
      remove_virtual_functions(new_table, new_goto_functions);

      bool found_function = false;
      for(const auto &fun : new_goto_functions.function_map)
      {
        if(fun.first == function_name)
        {
          const goto_programt &goto_program = fun.second.body;
          found_function = true;
          for(const auto &instruction : goto_program.instructions)
          {
            // There should be two guarded GOTOs with non-constant guards. One
            // branching for class C and one for class D or O.
            if(instruction.type == goto_program_instruction_typet::GOTO)
            {
              if(instruction.guard.id() == ID_equal)
              {
                THEN("Class C should call its specific method")
                {
                  const equal_exprt &eq_expr = to_equal_expr(instruction.guard);
                  check_function_call(
                    eq_expr,
                    "java::C",
                    "java::C.toString:()Ljava/lang/String;",
                    instruction.targets);
                }
              }

              else if(instruction.guard.id() == ID_or)
              {
                THEN("Classes D and O should both call O.toString()")
                {
                  const or_exprt &disjunction = to_or_expr(instruction.guard);
                  REQUIRE(
                    (disjunction.op0().id() == ID_equal &&
                     disjunction.op1().id() == ID_equal));
                  const equal_exprt &eq_expr0 =
                    to_equal_expr(disjunction.op0());
                  const equal_exprt &eq_expr1 =
                    to_equal_expr(disjunction.op1());

                  check_function_call(
                    eq_expr0,
                    "java::D",
                    "java::O.toString:()Ljava/lang/String;",
                    instruction.targets);
                  check_function_call(
                    eq_expr1,
                    "java::O",
                    "java::O.toString:()Ljava/lang/String;",
                    instruction.targets);
                }
              }
            }
          }
        }
      }

      REQUIRE(found_function);
    }
  }
}
