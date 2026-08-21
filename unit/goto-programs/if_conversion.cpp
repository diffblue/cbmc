/*******************************************************************\

Module: Unit tests for if_conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/namespace.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_instruction_code.h>
#include <goto-programs/goto_program.h>
#include <goto-programs/if_conversion.h>

#include <testing-utils/use_catch.h>

static std::size_t count_gotos(const goto_programt &p)
{
  std::size_t n = 0;
  for(const auto &i : p.instructions)
    if(i.is_goto())
      ++n;
  return n;
}

static bool has_conditional_assignment(const goto_programt &p)
{
  for(const auto &i : p.instructions)
    if(i.is_assign() && i.assign_rhs().id() == ID_if)
      return true;
  return false;
}

SCENARIO("if_conversion", "[core][goto-programs][if_conversion]")
{
  const signedbv_typet int_type{32};
  symbol_tablet symbol_table;
  symbolt x_symbol{"x", int_type, ID_C};
  symbol_table.insert(x_symbol);
  const symbol_exprt x = x_symbol.symbol_expr();
  symbolt c_symbol{"c", bool_typet{}, ID_C};
  symbol_table.insert(c_symbol);
  const symbol_exprt c = c_symbol.symbol_expr();
  const namespacet ns(symbol_table);

  GIVEN("a conditional assignment `if(c) x = 1;`")
  {
    goto_programt p;
    p.add(goto_programt::make_assignment(x, from_integer(1, int_type)));
    const auto join = p.add(goto_programt::make_skip());
    p.add(goto_programt::make_end_function());
    // jump over the assignment when !c (so the assignment runs when c)
    p.insert_before(
      p.instructions.begin(), goto_programt::make_goto(join, not_exprt{c}));
    p.update();

    REQUIRE(count_gotos(p) == 1);

    WHEN("if-conversion is applied")
    {
      const std::size_t converted = if_conversion(p, symbol_table, ID_C, ns);

      THEN("the branch is replaced by a guarded assignment")
      {
        REQUIRE(converted == 1);
        REQUIRE(count_gotos(p) == 0);
        REQUIRE(has_conditional_assignment(p));
      }
    }
  }

  GIVEN("a conditional region containing a function call")
  {
    symbolt f_symbol{"f", code_typet{{}, empty_typet{}}, ID_C};
    symbol_table.insert(f_symbol);
    const namespacet ns2(symbol_table);

    goto_programt p;
    p.add(goto_programt::make_function_call(
      code_function_callt{f_symbol.symbol_expr(), {}}));
    p.add(goto_programt::make_assignment(x, from_integer(1, int_type)));
    const auto join = p.add(goto_programt::make_skip());
    p.add(goto_programt::make_end_function());
    p.insert_before(
      p.instructions.begin(), goto_programt::make_goto(join, not_exprt{c}));
    p.update();

    WHEN("if-conversion is applied")
    {
      const std::size_t converted = if_conversion(p, symbol_table, ID_C, ns2);

      THEN("the region is not linearisable and the branch is kept")
      {
        REQUIRE(converted == 0);
        REQUIRE(count_gotos(p) == 1);
        REQUIRE_FALSE(has_conditional_assignment(p));
      }
    }
  }

  // Build the GOTO for `if(c) x = a; else x = b;`:
  //   IF !c GOTO else
  //   x = a
  //   GOTO join
  //   else: x = b
  //   join: skip
  const auto build_if_else =
    [&](goto_programt &p, const exprt &a, const exprt &b)
  {
    const auto then_assign = p.add(goto_programt::make_assignment(x, a));
    const auto then_goto = p.add(goto_programt::make_goto(then_assign));
    const auto else_assign = p.add(goto_programt::make_assignment(x, b));
    const auto join = p.add(goto_programt::make_skip());
    p.add(goto_programt::make_end_function());
    then_goto->set_target(join);
    p.insert_before(
      then_assign, goto_programt::make_goto(else_assign, not_exprt{c}));
    p.update();
  };

  GIVEN("an if/else assigning the same variable the same value")
  {
    // if(c) x = 1; else x = 1;
    goto_programt p;
    build_if_else(p, from_integer(1, int_type), from_integer(1, int_type));
    REQUIRE(count_gotos(p) == 2);

    WHEN("if-conversion is applied")
    {
      const std::size_t converted = if_conversion(p, symbol_table, ID_C, ns);

      THEN("both branches collapse into a single constant assignment")
      {
        REQUIRE(converted == 1);
        REQUIRE(count_gotos(p) == 0);
        // c ? 1 : 1 simplifies to the constant 1; no symbolic conditional is
        // left to defeat constant propagation (regression for return4).
        REQUIRE_FALSE(has_conditional_assignment(p));
      }
    }
  }

  GIVEN("an if/else assigning the same variable different values")
  {
    // if(c) x = 1; else x = 2;
    goto_programt p;
    build_if_else(p, from_integer(1, int_type), from_integer(2, int_type));
    REQUIRE(count_gotos(p) == 2);

    WHEN("if-conversion is applied")
    {
      const std::size_t converted = if_conversion(p, symbol_table, ID_C, ns);

      THEN("the pair becomes a single guarded (ternary) assignment")
      {
        REQUIRE(converted == 1);
        REQUIRE(count_gotos(p) == 0);
        REQUIRE(has_conditional_assignment(p));
        // exactly one assignment carries the ternary; the other arm is a skip
        std::size_t conditional_assignments = 0;
        for(const auto &i : p.instructions)
          if(i.is_assign() && i.assign_rhs().id() == ID_if)
            ++conditional_assignments;
        REQUIRE(conditional_assignments == 1);
      }
    }
  }
}
