/*******************************************************************\

Module: Unit tests for symex_assign

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <analyses/dirty.h>
#include <analyses/guard.h>
#include <goto-symex/expr_skeleton.h>
#include <goto-symex/goto_symex.h>
#include <goto-symex/goto_symex_state.h>
#include <goto-symex/symex_assign.h>
#include <goto-symex/symex_target.h>
#include <util/arith_tools.h>
#include <util/c_types.h>
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
  "symex_assignt::assign_symbol",
  "[core][goto-symex][symex-assign][symex-assign-symbol]")
{
  // Note that the initialization part of this test is very similar to that of
  // goto_symex_state.cpp

  // Initialize goto state
  std::list<goto_programt::instructiont> target;
  symex_targett::sourcet source{"fun", target.begin()};
  guard_managert manager;
  std::size_t fresh_name_count = 1;
  auto fresh_name = [&fresh_name_count](const irep_idt &) {
    return fresh_name_count++;
  };
  goto_symex_statet state{
    source, DEFAULT_MAX_FIELD_SENSITIVITY_ARRAY_SIZE, manager, fresh_name};

  // Initialize dirty field of state
  incremental_dirtyt dirty;
  goto_functiont function;
  dirty.populate_dirty_for_function("fun", function);
  state.dirty = &dirty;

  // Initialize symbol table with an integer symbol `foo`, and a boolean g
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  const signedbv_typet int_type{32};
  const symbol_exprt foo{"foo", int_type};
  add_to_symbol_table(symbol_table, foo);
  const ssa_exprt ssa_foo{foo};
  const symbol_exprt g{"g", bool_typet{}};
  add_to_symbol_table(symbol_table, g);

  optionst options;
  symex_configt symex_config{options};

  GIVEN("An L1 lhs and an L2 rhs of type int, and a guard g")
  {
    exprt::operandst guard;
    guard.push_back(g);
    symex_target_equationt target_equation{null_message_handler};

    WHEN("Symbol `foo` is assigned constant integer `475`")
    {
      const exprt rhs1 = from_integer(475, int_type);
      symex_assignt{state,
                    symex_targett::assignment_typet::STATE,
                    ns,
                    symex_config,
                    target_equation}
        .assign_symbol(ssa_foo, expr_skeletont{}, rhs1, guard);
      THEN("An equation is added to the target")
      {
        REQUIRE(target_equation.SSA_steps.size() == 1);
        SSA_stept step = target_equation.SSA_steps.back();
        REQUIRE(step.type == goto_trace_stept::typet::ASSIGNMENT);
        REQUIRE(step.assignment_type == symex_targett::assignment_typet::STATE);
        REQUIRE(step.cond_expr == equal_exprt{step.ssa_lhs, step.ssa_rhs});
        REQUIRE(step.guard == g);

        THEN("The left-hand-side of the equation is foo!0#1")
        {
          REQUIRE(to_symbol_expr(step.ssa_lhs).get_identifier() == "foo!0#1");
        }
        THEN("The right-hand-side of the equation is g!0#0 ? 475 : foo!0#0")
        {
          const if_exprt *rhs_if =
            expr_try_dynamic_cast<if_exprt>(step.ssa_rhs);
          REQUIRE(rhs_if != nullptr);
          REQUIRE(to_symbol_expr(rhs_if->cond()).get_identifier() == "g!0#0");
          const auto then_value =
            numeric_cast_v<mp_integer>(to_constant_expr(rhs_if->true_case()));
          REQUIRE(then_value == 475);
          const symbol_exprt rhs_symbol = to_symbol_expr(rhs_if->false_case());
          REQUIRE(rhs_symbol.get_identifier() == "foo!0#0");
        }
        THEN("ssa_full_lhs is foo!0#1")
        {
          REQUIRE(
            to_symbol_expr(step.ssa_full_lhs).get_identifier() == "foo!0#1");
        }
        THEN("original_full_lhs is foo")
        {
          REQUIRE(
            to_symbol_expr(step.original_full_lhs).get_identifier() == "foo");
        }
      }
    }
  }
  GIVEN(
    "A lhs and rhs of type int, an empty guard, and constant propagation "
    "activated")
  {
    exprt::operandst guard;
    symex_config.constant_propagation = true;
    WHEN("foo is assigned without a guard")
    {
      const exprt rhs1 = from_integer(5721, int_type);
      symex_target_equationt target_equation{null_message_handler};
      symex_assignt symex_assign{state,
                                 symex_targett::assignment_typet::STATE,
                                 ns,
                                 symex_config,
                                 target_equation};
      symex_assign.assign_symbol(ssa_foo, expr_skeletont{}, rhs1, guard);
      THEN("An equation with an empty guard is added to the target")
      {
        REQUIRE(target_equation.SSA_steps.size() == 1);
        SSA_stept step = target_equation.SSA_steps.back();
        REQUIRE(step.guard == true_exprt{});
      }
      THEN("The propagation map maps 'foo' to 5721")
      {
        const auto propagated = state.rename(ssa_foo, ns);
        const mp_integer value =
          numeric_cast_v<mp_integer>(to_constant_expr(propagated.get()));
        REQUIRE(value == 5721);
        WHEN("foo is assigned a second time")
        {
          const exprt rhs2 = from_integer(1841, int_type);
          symex_assign.assign_symbol(ssa_foo, expr_skeletont{}, rhs2, guard);
          THEN("A second equation is added to the target")
          {
            REQUIRE(target_equation.SSA_steps.size() == 2);
            SSA_stept step = target_equation.SSA_steps.back();
            REQUIRE(step.type == goto_trace_stept::typet::ASSIGNMENT);
            REQUIRE(
              step.assignment_type == symex_targett::assignment_typet::STATE);
            REQUIRE(step.cond_expr.id() == ID_equal);
            REQUIRE(step.cond_expr == equal_exprt{step.ssa_lhs, step.ssa_rhs});
            REQUIRE(step.guard == true_exprt{});

            THEN("The left-hand-side of the equation is foo!0#2")
            {
              REQUIRE(
                to_symbol_expr(step.ssa_lhs).get_identifier() == "foo!0#2");
            }
            THEN("The right-hand-side of the equation is 1841")
            {
              const auto rhs_value =
                numeric_cast_v<mp_integer>(to_constant_expr(step.ssa_rhs));
              REQUIRE(rhs_value == 1841);
            }
            THEN("ssa_full_lhs is foo!0#1")
            {
              REQUIRE(
                to_symbol_expr(step.ssa_full_lhs).get_identifier() ==
                "foo!0#2");
            }
            THEN("original_full_lhs is foo")
            {
              REQUIRE(
                to_symbol_expr(step.original_full_lhs).get_identifier() ==
                "foo");
            }
          }
        }
      }
    }
  }
  GIVEN(
    "A symbol `struct1` a with_exprt `struct1 with [field1 <- 234]` and "
    "a skeleton `☐.field_1`")
  {
    struct_union_typet::componentst components;
    components.emplace_back("field1", int_type);
    const struct_typet struct_type{components};
    const symbol_exprt struct1_sym{"struct1", struct_type};
    add_to_symbol_table(symbol_table, struct1_sym);
    const with_exprt rhs{
      struct1_sym, member_designatort{"field1"}, from_integer(234, int_type)};
    expr_skeletont skeleton =
      expr_skeletont::remove_op0(member_exprt{struct1_sym, components.back()});
    const ssa_exprt struct1_ssa{struct1_sym};

    exprt::operandst guard;
    symex_target_equationt target_equation{null_message_handler};

    WHEN("Symbol `struct1` is assigned `struct1 with [field1 <- 234]`")
    {
      symex_assignt{state,
                    symex_targett::assignment_typet::STATE,
                    ns,
                    symex_config,
                    target_equation}
        .assign_symbol(struct1_ssa, skeleton, rhs, guard);
      THEN("Two equations are added to the target")
      {
        REQUIRE(target_equation.SSA_steps.size() == 2);
        SSA_stept assign_step = target_equation.SSA_steps.front();
        SSA_stept expand_step = target_equation.SSA_steps.back();
        THEN("Assign step LHS is `struct1!0#1`")
        {
          REQUIRE(assign_step.ssa_lhs.get_identifier() == "struct1!0#1");
        }
        THEN("Assign step original full LHS is `struct1.field1`")
        {
          REQUIRE(
            assign_step.original_full_lhs ==
            member_exprt{struct1_sym, "field1", int_type});
        }
        THEN("Assign step SSA full LHS is `struct1!0#1`")
        {
          const auto as_symbol =
            expr_try_dynamic_cast<symbol_exprt>(assign_step.ssa_lhs);
          REQUIRE(as_symbol);
          REQUIRE(as_symbol->get_identifier() == "struct1!0#1");
        }
        THEN("Assign step RHS is { struct1!0#0..field1 } with field1 = 234")
        {
          ssa_exprt struct1_v0_field1{
            member_exprt{struct1_sym, "field1", int_type}};
          struct1_v0_field1.set_level_0(0);
          struct1_v0_field1.set_level_2(0);
          struct_exprt struct_expr(struct_type);
          struct_expr.add_to_operands(struct1_v0_field1);
          with_exprt struct1_v0_with_field_set = rhs;
          struct1_v0_with_field_set.old() = struct_expr;
          REQUIRE(assign_step.ssa_rhs == struct1_v0_with_field_set);
        }
        THEN("Expand step LHS is `struct1!0#2..field1`")
        {
          REQUIRE(
            expand_step.ssa_lhs.get_identifier() == "struct1!0#2..field1");
        }
        THEN("Expand step original full LHS is `struct1.field1`")
        {
          REQUIRE(
            expand_step.original_full_lhs ==
            member_exprt{struct1_sym, "field1", int_type});
        }
        THEN("Expand step SSA full LHS is `struct1!0#2..field1`")
        {
          const auto as_symbol =
            expr_try_dynamic_cast<symbol_exprt>(expand_step.ssa_lhs);
          REQUIRE(as_symbol);
          REQUIRE(as_symbol->get_identifier() == "struct1!0#2..field1");
        }
        THEN("Expand step RHS is struct1!0#1.field1")
        {
          ssa_exprt struct1_v1{struct1_sym};
          struct1_v1.set_level_0(0);
          struct1_v1.set_level_2(1);
          REQUIRE(
            expand_step.ssa_rhs ==
            member_exprt{struct1_v1, "field1", int_type});
        }
      }
    }
  }
}
