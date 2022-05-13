/*******************************************************************\

Module: Unit tests for java_types

Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_virtual_functions.h>
#include <util/config.h>
#include <goto-instrument/cover.h>
#include <util/options.h>

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
    REQUIRE(target->type() == goto_program_instruction_typet::FUNCTION_CALL);
    REQUIRE(target->call_function().id() == ID_symbol);
    REQUIRE(
      to_symbol_expr(target->call_function()).get_identifier() ==
      function_name);
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
      goto_functionst new_goto_functions;
      goto_convert(new_table, new_goto_functions, null_message_handler);
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
            if(instruction.type() == goto_program_instruction_typet::GOTO)
            {
              if(instruction.condition().id() == ID_equal)
              {
                THEN("Class C should call its specific method")
                {
                  const equal_exprt &eq_expr =
                    to_equal_expr(instruction.condition());
                  check_function_call(
                    eq_expr,
                    "java::C",
                    "java::C.toString:()Ljava/lang/String;",
                    instruction.targets);
                }
              }

              else if(instruction.condition().id() == ID_or)
              {
                THEN("Classes D and O should both call O.toString()")
                {
                  const or_exprt &disjunction =
                    to_or_expr(instruction.condition());
                  REQUIRE(
                    (disjunction.op0().id() == ID_equal &&
                     disjunction.op1().id() == ID_equal));
                  equal_exprt eq_expr0 =
                    to_equal_expr(disjunction.op0());
                  equal_exprt eq_expr1 =
                    to_equal_expr(disjunction.op1());

                  if(eq_expr0.op0().id() == ID_constant &&
                     to_constant_expr(eq_expr0.op0()).get_value() == "java::O")
                  {
                    // Allow either order of the D and O comparisons:
                    std::swap(eq_expr0, eq_expr1);
                  }

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

      WHEN("basic blocks are instrumented")
      {
        optionst options;
        options.set_option("cover", "location");
        const auto cover_config =
          get_cover_config(options, new_table, null_message_handler);
        REQUIRE_FALSE(instrument_cover_goals(
          cover_config, new_table, new_goto_functions, null_message_handler));

        auto function = new_goto_functions.function_map.find(function_name);
        REQUIRE(function != new_goto_functions.function_map.end());

        const goto_programt &goto_program = function->second.body;
        // Skip the first instruction which is a declaration with no location
        auto it = std::next(goto_program.instructions.begin());
        REQUIRE(it != goto_program.instructions.end());

        THEN(
          "Each instruction with a new bytecode index begins with ASSERT"
          " and coverage assertions are at the beginning of the block")
        {
          irep_idt current_index;

          while(it->type() != goto_program_instruction_typet::END_FUNCTION)
          {
            const source_locationt &loc = it->source_location();
            REQUIRE(loc != source_locationt::nil());
            REQUIRE_FALSE(loc.get_java_bytecode_index().empty());
            const auto new_index = loc.get_java_bytecode_index();

            if(new_index != current_index)
            {
              current_index = new_index;
              // instruction with a new bytecode index begins with ASSERT
              REQUIRE(it->type() == goto_program_instruction_typet::ASSERT);
              // the assertion corresponds to a line coverage goal
              REQUIRE_FALSE(loc.get_basic_block_source_lines().is_nil());
            }
            else
            {
              // there is no line coverage goal in the middle of a block
              REQUIRE(loc.get_basic_block_source_lines().is_nil());
            }

            ++it;
          }
        }
      }
    }
  }
}
