/*******************************************************************\

Module: Unit tests for goto_symex_statet

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <analyses/dirty.h>
#include <goto-symex/goto_symex_state.h>
#include <util/arith_tools.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

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
  "Goto symex state assignment",
  "[core][goto-symex][goto-symex-state][assignment]")
{
  // Initialize goto state
  std::list<goto_programt::instructiont> target;
  symex_targett::sourcet source{"fun", target.begin()};
  guard_managert manager;
  std::size_t fresh_name_count = 1;
  auto fresh_name = [&fresh_name_count](const irep_idt &) {
    return fresh_name_count++;
  };
  goto_symex_statet state{source, manager, fresh_name};

  // Initialize dirty field of state
  incremental_dirtyt dirty;
  goto_functiont function;
  dirty.populate_dirty_for_function("fun", function);
  state.dirty = &dirty;

  GIVEN("An L1 lhs and an L2 rhs of type int")
  {
    // Initialize symbol table with an integer symbol `foo`
    symbol_tablet symbol_table;
    namespacet ns{symbol_table};
    const signedbv_typet int_type{32};
    const symbol_exprt foo{"foo", int_type};
    add_to_symbol_table(symbol_table, foo);
    const ssa_exprt ssa_foo{foo};

    WHEN("Symbol `foo` is assigned constant integer `475`")
    {
      const exprt rhs1 = from_integer(475, int_type);
      const auto result =
        state.assignment(ssa_foo, rhs1, ns, true, true, false);
      THEN("The result is `foo` renamed to L2")
      {
        REQUIRE(result.get().get_identifier() == "foo!0#1");
      }
      THEN("The propagation map contains an entry for `foo`")
      {
        const auto l1_foo = state.rename_ssa<L1>(ssa_foo, ns);
        const auto foo_propagated =
          state.propagation.find(l1_foo.get().get_identifier());
        REQUIRE(foo_propagated.has_value());
        const auto foo_value =
          numeric_cast_v<mp_integer>(to_constant_expr(foo_propagated->get()));
        REQUIRE(foo_value == 475);
      }
      THEN("Symbol `foo` is assigned another integer 1834")
      {
        const exprt rhs2 = from_integer(1834, int_type);
        const auto result2 =
          state.assignment(ssa_foo, rhs2, ns, true, true, false);

        THEN("The level 2 index of `foo` is incremented")
        {
          REQUIRE(result2.get().get_identifier() == "foo!0#2");
        }
        THEN("The propagation map entry for `foo` is updated")
        {
          const auto l1_foo = state.rename_ssa<L1>(ssa_foo, ns);
          const auto foo_propagated =
            state.propagation.find(l1_foo.get().get_identifier());
          REQUIRE(foo_propagated.has_value());
          const auto foo_value =
            numeric_cast_v<mp_integer>(to_constant_expr(foo_propagated->get()));
          REQUIRE(foo_value == 1834);
        }
      }
    }
  }
}
