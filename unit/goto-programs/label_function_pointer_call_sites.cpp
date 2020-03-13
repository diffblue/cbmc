/*******************************************************************\

Module: Label function pointer call sites unit tests

Author: Daniel Poetzl

\*******************************************************************/

#include <testing-utils/get_goto_model_from_c.h>
#include <testing-utils/use_catch.h>

#include <goto-programs/label_function_pointer_call_sites.h>

TEST_CASE("Label function pointer call sites", "[core]")
{
  const std::string code = R"(
    void f() {}
    void g() {}

    void h()
    {
      f();
      void (*fp)() = f;
      fp();
      (1 ? f : g)();
    }

    void main() { h(); }
  )";

  goto_modelt goto_model = get_goto_model_from_c(code);

  label_function_pointer_call_sites(goto_model);

  auto &h = goto_model.goto_functions.function_map.at("h");

  for_each_instruction_if(
    h,
    [](goto_programt::const_targett it) { return it->is_function_call(); },
    [](goto_programt::const_targett it) {
      static int call_count = 0;

      switch (call_count)
      {
      case 0:
        // first call instruction
        REQUIRE(it->get_function_call().function().id() == ID_symbol);
        break;
      case 1:
      {
        // second call instruction
        const auto &fp_symbol =
          to_symbol_expr(
            to_dereference_expr(it->get_function_call().function()).pointer())
            .get_identifier();
        REQUIRE(fp_symbol == "h.function_pointer_call.1");
        break;
      }
      case 2:
      {
        // third call instruction
        const auto &fp_symbol =
          to_symbol_expr(
            to_dereference_expr(it->get_function_call().function()).pointer())
            .get_identifier();
        REQUIRE(fp_symbol == "h.function_pointer_call.2");

        auto it_prev = std::prev(it);
        const auto &assign = it_prev->get_assign();

        const auto &lhs = assign.lhs();
        const auto &rhs = assign.rhs();

        REQUIRE(
          to_symbol_expr(lhs).get_identifier() == "h.function_pointer_call.2");

        REQUIRE(rhs.id() == ID_if);

        break;
      }
      default:
        break;
      }

      call_count++;
    }
  );
}
