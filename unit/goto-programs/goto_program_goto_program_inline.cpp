/*******************************************************************\

Module: Inline calls in program unit tests

Author: Remi Delmas

\*******************************************************************/

#include <util/message.h>

#include <goto-programs/goto_inline.h>

#include <testing-utils/get_goto_model_from_c.h>
#include <testing-utils/use_catch.h>

TEST_CASE("Goto program inline", "[core][goto-programs][goto_program_inline]")
{
  const std::string code = R"(
    int x;
    int y;
    void f() { y = 0; }
    void g() { x = 0; f(); }
    void h() { g(); }
    void main() { h(); }
  )";

  goto_modelt goto_model = get_goto_model_from_c(code);

  auto &function = goto_model.goto_functions.function_map.at("h");

  null_message_handlert message_handler;
  goto_program_inline(
    goto_model.goto_functions,
    function.body,
    namespacet(goto_model.symbol_table),
    message_handler);

  static int assign_count = 0;
  for_each_instruction_if(
    function,
    [&](goto_programt::const_targett it) {
      return it->is_function_call() || it->is_assign();
    },
    [&](goto_programt::const_targett it) {
      if(it->is_function_call())
      {
        // there are no calls left
        FAIL();
      }

      if(it->is_assign())
      {
        // the two assignments were inlined
        const auto &lhs = it->assign_lhs();
        if(assign_count == 0)
        {
          REQUIRE(to_symbol_expr(lhs).get_identifier() == "x");
        }
        else if(assign_count == 1)
        {
          REQUIRE(to_symbol_expr(lhs).get_identifier() == "y");
        }
        assign_count++;
      }
    });
  REQUIRE(assign_count == 2);
}
