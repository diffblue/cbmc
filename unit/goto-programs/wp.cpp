/*******************************************************************\

Module: Unit tests for weakest precondition

Author: Diffblue Ltd.

\*******************************************************************/

#include <util/cmdline.h>
#include <util/config.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <goto-programs/wp.h>

#include <ansi-c/ansi_c_language.h>
#include <ansi-c/goto-conversion/goto_convert_functions.h>
#include <langapi/mode.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <sstream>

namespace
{
/// Parse the C `source` -- which must define a function `f` containing an
/// assignment immediately followed by an assertion -- build its goto program,
/// and return the simplified weakest precondition of that assignment with
/// respect to the asserted condition.
exprt simplified_wp_of_first_assignment(const std::string &source)
{
  config = configt{};
  cmdlinet cmdline;
  config.set(cmdline);

  if(get_language_from_mode(ID_C) == nullptr)
    register_language(new_ansi_c_language);

  ansi_c_languaget language;

  std::istringstream in(source);
  REQUIRE_FALSE(language.parse(in, "", null_message_handler));

  symbol_tablet symbol_table;
  REQUIRE_FALSE(language.typecheck(symbol_table, "", null_message_handler));

  goto_functionst goto_functions;
  goto_convert(symbol_table, goto_functions, null_message_handler);

  const auto f_it = goto_functions.function_map.find("f");
  REQUIRE(f_it != goto_functions.function_map.end());

  const goto_programt &p = f_it->second.body;
  const namespacet ns(symbol_table);

  forall_goto_program_instructions(it, p)
  {
    if(!it->is_assign())
      continue;

    auto next_it = it;
    ++next_it;

    if(next_it != p.instructions.end() && next_it->is_assert())
      return simplify_expr(wp(it->code(), next_it->condition(), ns), ns);
  }

  // no assignment-followed-by-assertion pair found
  REQUIRE(false);
  return nil_exprt{};
}
} // namespace

TEST_CASE(
  "Weakest precondition of a constant assignment",
  "[core][goto-programs][wp]")
{
  // wp(x = 1, x == 1) is (1 == 1), which simplifies to true.
  const exprt pre = simplified_wp_of_first_assignment(
    "void f() { int x; x = 1; assert(x == 1); }\n");
  REQUIRE(pre.is_true());
}

TEST_CASE(
  "Weakest precondition of an initialised local",
  "[core][goto-programs][wp]")
{
  // wp(y = 5, y > 0) is (5 > 0), which simplifies to true.
  const exprt pre = simplified_wp_of_first_assignment(
    "void f() { int y = 5; assert(y > 0); }\n");
  REQUIRE(pre.is_true());
}
