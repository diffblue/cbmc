/*******************************************************************\

Module: Unit tests for goto_programt copy constructor

Author: Diffblue Ltd.

\*******************************************************************/

#include <goto-programs/goto_program.h>
#include <testing-utils/get_goto_model_from_c.h>
#include <testing-utils/use_catch.h>
#include <util/arith_tools.h>
#include <util/cmdline.h>
#include <util/config.h>
#include <util/std_expr.h>

TEST_CASE(
  "We can copy an empty goto program",
  "[core][goto-programs][goto-program-copy]")
{
  auto const original_goto_program = goto_programt{};
  auto const copy = original_goto_program;
  REQUIRE(copy.empty());
}

TEST_CASE(
  "We can copy a non-empty goto program that does not have jumps",
  "[core][goto-programs][goto-program-copy]")
{
  config.set(cmdlinet{});
  auto const original_goto_model = get_goto_model_from_c(
    "int main(void) {\n"
    "  int x = 0;\n"
    "  int y = x + 1;\n"
    "  return y;\n"
    "}\n");
  auto const &original_goto_program = original_goto_model.get_goto_functions()
                                        .function_map.find("main")
                                        ->second.body;
  goto_programt goto_program_copy = original_goto_program;
  auto original_it = original_goto_program.instructions.begin();
  auto copy_it = goto_program_copy.instructions.begin();
  for(; original_it != original_goto_program.instructions.end() &&
        copy_it != goto_program_copy.instructions.end();
      ++original_it, ++copy_it)
  {
    // Check that all instructions in both programs have the same type
    REQUIRE(original_it->type == copy_it->type);
  }
  // Check that both goto programs have the same number of instructions
  REQUIRE(original_it == original_goto_program.instructions.end());
  REQUIRE(copy_it == goto_program_copy.instructions.end());
}

TEST_CASE(
  "We can copy a goto-program with jumps",
  "[core][goto-programs][goto-program-copy]")
{
  config.set(cmdlinet{});
  auto const original_goto_model = get_goto_model_from_c(
    "#include <assert.h>\n"
    "\n"
    "int main(void) {\n"
    "  int x = 0;\n"
    "  int y = 1;\n"
    "  const int n = 10;\n"
    "  for(int i = 0; i < n; ++i) {\n"
    "    int tmp = y;\n"
    "    y += x;\n"
    "    x = tmp;\n"
    "  }\n"
    "  assert(y == 55);\n"
    "}\n");
  auto const &original_goto_program = original_goto_model.get_goto_functions()
                                        .function_map.find("main")
                                        ->second.body;
  goto_programt goto_program_copy = original_goto_program;
  auto original_it = original_goto_program.instructions.begin();
  auto copy_it = goto_program_copy.instructions.begin();
  for(; original_it != original_goto_program.instructions.end() &&
        copy_it != goto_program_copy.instructions.end();
      ++original_it, ++copy_it)
  {
    // Check that all instructions in both programs have the same type
    REQUIRE(original_it->type == copy_it->type);

    // check that the targets for all instructions match in original and copy
    REQUIRE(original_it->targets.size() == copy_it->targets.size());
    auto original_target_it = original_it->targets.begin();
    auto copy_target_it = copy_it->targets.begin();

    for(; original_target_it != original_it->targets.end() &&
          copy_target_it != copy_it->targets.end();
        ++original_target_it, ++copy_target_it)
    {
      REQUIRE((*original_target_it)->type == (*copy_target_it)->type);
    }
    REQUIRE(copy_target_it == copy_it->targets.end());
    REQUIRE(original_target_it == original_it->targets.end());
  }
  // Check that both goto programs have the same number of instructions
  REQUIRE(original_it == original_goto_program.instructions.end());
  REQUIRE(copy_it == goto_program_copy.instructions.end());
}
