/*******************************************************************\

Module: Unit tests for goto_statet::apply_condition

Author: Owen Mansel-Chan, owen.mansel-chan@diffblue.com

\*******************************************************************/

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <goto-symex/goto_symex.h>

static void add_to_symbol_table(
  symbol_tablet &symbol_table,
  const symbol_exprt &symbol_expr)
{
  symbolt symbol;
  symbol.name = symbol_expr.get_identifier();
  symbol.type = symbol_expr.type();
  symbol.value = symbol_expr;
  symbol.is_thread_local = true;
  symbol_table.insert(symbol);
}

SCENARIO(
  "Apply condition and update constant propagator and value-set",
  "[core][goto-symex][apply_condition]")
{
  const symbol_exprt b{"b", bool_typet{}};
  const symbol_exprt c{"c", bool_typet{}};

  // Add symbols to symbol table
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  add_to_symbol_table(symbol_table, b);
  add_to_symbol_table(symbol_table, c);

  // Initialize goto state
  std::list<goto_programt::instructiont> target;
  symex_targett::sourcet source{"fun", target.begin()};
  guard_managert guard_manager;
  std::size_t count = 0;
  auto fresh_name = [&count](const irep_idt &) { return count++; };
  goto_symex_statet state{source,
                          DEFAULT_MAX_FIELD_SENSITIVITY_ARRAY_SIZE,
                          guard_manager,
                          fresh_name};

  goto_statet goto_state{state};
  const exprt renamed_b = state.rename<L2>(b, ns).get();
  const exprt renamed_c = state.rename<L2>(c, ns).get();

  WHEN("Applying the condition 'b'")
  {
    const exprt condition = renamed_b;
    goto_state.apply_condition(condition, state, ns);

    THEN("b should be in the constant propagator with value 'true'")
    {
      auto it = goto_state.propagation.find(
        to_ssa_expr(renamed_b).get_l1_object_identifier());
      REQUIRE(it);
      REQUIRE(it->get() == true_exprt{});
    }
  }

  WHEN("Applying the condition '!b'")
  {
    const exprt condition = not_exprt{renamed_b};
    goto_state.apply_condition(condition, state, ns);

    THEN("b should be in the constant propagator with value 'false'")
    {
      auto it = goto_state.propagation.find(
        to_ssa_expr(renamed_b).get_l1_object_identifier());
      REQUIRE(it);
      REQUIRE(it->get() == false_exprt{});
    }
  }

  WHEN("Applying the condition 'b == true'")
  {
    const exprt condition = equal_exprt{renamed_b, true_exprt{}};
    goto_state.apply_condition(condition, state, ns);

    THEN("b should be in the constant propagator with value 'true'")
    {
      auto it = goto_state.propagation.find(
        to_ssa_expr(renamed_b).get_l1_object_identifier());
      REQUIRE(it);
      REQUIRE(it->get() == true_exprt{});
    }
  }

  WHEN("Applying the condition 'b == false'")
  {
    const exprt condition = equal_exprt{renamed_b, false_exprt{}};
    goto_state.apply_condition(condition, state, ns);

    THEN("b should be in the constant propagator with value 'false'")
    {
      auto it = goto_state.propagation.find(
        to_ssa_expr(renamed_b).get_l1_object_identifier());
      REQUIRE(it);
      REQUIRE(it->get() == false_exprt{});
    }
  }

  WHEN("Applying the condition '!(b == true)'")
  {
    const exprt condition = not_exprt{equal_exprt{renamed_b, true_exprt{}}};
    goto_state.apply_condition(condition, state, ns);

    THEN("b should be in the constant propagator with value 'false'")
    {
      auto it = goto_state.propagation.find(
        to_ssa_expr(renamed_b).get_l1_object_identifier());
      REQUIRE(it);
      REQUIRE(it->get() == false_exprt{});
    }
  }

  WHEN("Applying the condition '!(b == false)'")
  {
    const exprt condition = not_exprt{equal_exprt{renamed_b, false_exprt{}}};
    goto_state.apply_condition(condition, state, ns);

    THEN("b should be in the constant propagator with value 'true'")
    {
      auto it = goto_state.propagation.find(
        to_ssa_expr(renamed_b).get_l1_object_identifier());
      REQUIRE(it);
      REQUIRE(it->get() == true_exprt{});
    }
  }

  WHEN("Applying the condition 'b != true'")
  {
    const exprt condition = notequal_exprt{renamed_b, true_exprt{}};
    goto_state.apply_condition(condition, state, ns);

    THEN("b should be in the constant propagator with value 'false'")
    {
      auto it = goto_state.propagation.find(
        to_ssa_expr(renamed_b).get_l1_object_identifier());
      REQUIRE(it);
      REQUIRE(it->get() == false_exprt{});
    }
  }

  WHEN("Applying the condition 'b != false'")
  {
    const exprt condition = notequal_exprt{renamed_b, false_exprt{}};
    goto_state.apply_condition(condition, state, ns);

    THEN("b should be in the constant propagator with value 'true'")
    {
      auto it = goto_state.propagation.find(
        to_ssa_expr(renamed_b).get_l1_object_identifier());
      REQUIRE(it);
      REQUIRE(it->get() == true_exprt{});
    }
  }

  WHEN("Applying the condition '!(b != true)'")
  {
    const exprt condition = not_exprt{notequal_exprt{renamed_b, true_exprt{}}};
    goto_state.apply_condition(condition, state, ns);

    THEN("b should be in the constant propagator with value 'true'")
    {
      auto it = goto_state.propagation.find(
        to_ssa_expr(renamed_b).get_l1_object_identifier());
      REQUIRE(it);
      REQUIRE(it->get() == true_exprt{});
    }
  }

  WHEN("Applying the condition '!(b != false)'")
  {
    const exprt condition = not_exprt{notequal_exprt{renamed_b, false_exprt{}}};
    goto_state.apply_condition(condition, state, ns);

    THEN("b should be in the constant propagator with value 'false'")
    {
      auto it = goto_state.propagation.find(
        to_ssa_expr(renamed_b).get_l1_object_identifier());
      REQUIRE(it);
      REQUIRE(it->get() == false_exprt{});
    }
  }

  WHEN("Applying the condition 'b && c'")
  {
    const exprt condition = and_exprt{renamed_b, renamed_c};
    goto_state.apply_condition(condition, state, ns);

    THEN("b should be in the constant propagator with value 'true'")
    {
      auto it = goto_state.propagation.find(
        to_ssa_expr(renamed_b).get_l1_object_identifier());
      REQUIRE(it);
      REQUIRE(it->get() == true_exprt{});
    }
  }
}
