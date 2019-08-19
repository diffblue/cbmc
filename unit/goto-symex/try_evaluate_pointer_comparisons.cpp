/*******************************************************************\

Module: Unit tests for try_evaluate_pointer_comparisons

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <goto-symex/goto_symex.h>
#include <util/arith_tools.h>
#include <util/c_types.h>

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
  "Try to evaluate pointer comparisons",
  "[core][goto-symex][try_evaluate_pointer_comparisons]")
{
  const unsignedbv_typet int_type{32};
  const pointer_typet ptr_type = pointer_type(int_type);
  const symbol_exprt ptr1{"ptr1", ptr_type};
  const symbol_exprt ptr2{"ptr2", ptr_type};
  const symbol_exprt value1{"value1", int_type};
  const address_of_exprt address1{value1};
  const symbol_exprt value2{"value2", int_type};
  const address_of_exprt address2{value2};
  const symbol_exprt b{"b", bool_typet{}};
  const null_pointer_exprt null_ptr{ptr_type};

  // Add symbols to symbol table
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  add_to_symbol_table(symbol_table, ptr1);
  add_to_symbol_table(symbol_table, ptr2);
  add_to_symbol_table(symbol_table, value1);
  add_to_symbol_table(symbol_table, value2);
  add_to_symbol_table(symbol_table, b);

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

  GIVEN("A value set in which pointer symbol `ptr1` only points to `&value1`")
  {
    value_sett value_set;
    const renamedt<exprt, L1> ptr1_l1 = state.rename<L1>(ptr1, ns);
    const renamedt<exprt, L1> address1_l1 = state.rename<L1>(address1, ns);
    // ptr1 <- &value1
    value_set.assign(ptr1_l1.get(), address1_l1.get(), ns, false, false);

    WHEN("Evaluating ptr1 == &value1")
    {
      const equal_exprt comparison{ptr1, address1};
      const renamedt<exprt, L2> renamed_comparison =
        state.rename(comparison, ns);
      auto result = try_evaluate_pointer_comparisons(
        renamed_comparison, value_set, ID_java, ns);
      THEN("Evaluation succeeds")
      {
        REQUIRE(result.get() == true_exprt{});
      }
    }

    WHEN("Evaluating ptr1 == (long*)(short*)&value1")
    {
      const signedbv_typet long_type{64};
      const signedbv_typet short_type{16};
      const pointer_typet ptr_long_type = pointer_type(long_type);
      const pointer_typet ptr_short_type = pointer_type(short_type);
      const equal_exprt comparison{
        ptr1,
        typecast_exprt{typecast_exprt{address1, ptr_short_type},
                       ptr_long_type}};
      const renamedt<exprt, L2> renamed_comparison =
        state.rename(comparison, ns);
      auto result = try_evaluate_pointer_comparisons(
        renamed_comparison, value_set, ID_java, ns);
      THEN("Evaluation succeeds")
      {
        REQUIRE(result.get() == true_exprt{});
      }
    }

    WHEN("Evaluating ptr1 != &value1")
    {
      const notequal_exprt comparison{ptr1, address1};
      const renamedt<exprt, L2> renamed_comparison =
        state.rename(comparison, ns);
      auto result = try_evaluate_pointer_comparisons(
        renamed_comparison, value_set, ID_java, ns);
      THEN("Evaluation succeeds")
      {
        REQUIRE(result.get() == false_exprt{});
      }
    }

    WHEN("Evaluating ptr1 == ptr2")
    {
      const equal_exprt comparison{ptr1, ptr2};
      const renamedt<exprt, L2> renamed_comparison =
        state.rename(comparison, ns);
      auto result = try_evaluate_pointer_comparisons(
        renamed_comparison, value_set, ID_java, ns);
      THEN("Evaluation leaves the expression unchanged")
      {
        REQUIRE(result.get() == renamed_comparison.get());
      }
    }
  }

  GIVEN(
    "A value set in which pointer symbol `ptr1` can point to `&value1` or "
    "`&value2`")
  {
    value_sett value_set;
    const if_exprt if_expr{b, address1, address2};
    const renamedt<exprt, L1> ptr1_l1 = state.rename<L1>(ptr1, ns);
    const renamedt<exprt, L1> if_expr_l1 = state.rename<L1>(if_expr, ns);
    // ptr1 <- b ? &value1 : &value2
    value_set.assign(ptr1_l1.get(), if_expr_l1.get(), ns, false, false);

    WHEN("Evaluating ptr1 == &value1")
    {
      const equal_exprt comparison{ptr1, address1};
      const renamedt<exprt, L2> renamed_comparison =
        state.rename(comparison, ns);
      auto result = try_evaluate_pointer_comparisons(
        renamed_comparison, value_set, ID_java, ns);
      THEN("Evaluation leaves the expression unchanged")
      {
        REQUIRE(result.get() == renamed_comparison.get());
      }
    }

    WHEN("Evaluating ptr1 != &value1")
    {
      const notequal_exprt comparison{ptr1, address1};
      const renamedt<exprt, L2> renamed_comparison =
        state.rename(comparison, ns);
      auto result = try_evaluate_pointer_comparisons(
        renamed_comparison, value_set, ID_java, ns);
      THEN("Evaluation leaves the expression unchanged")
      {
        REQUIRE(result.get() == renamed_comparison.get());
      }
    }

    WHEN("Evaluating ptr1 != nullptr")
    {
      const notequal_exprt comparison{ptr1, null_ptr};
      const renamedt<exprt, L2> renamed_comparison =
        state.rename(comparison, ns);
      auto result = try_evaluate_pointer_comparisons(
        renamed_comparison, value_set, ID_java, ns);
      THEN("Evaluation succeeds")
      {
        REQUIRE(result.get() == true_exprt{});
      }
    }
  }

  GIVEN(
    "A value set in which pointer symbol `ptr1` can point to `&value1` or "
    "`unknown`")
  {
    value_sett value_set;
    const exprt unknown_expr{ID_unknown, ptr_type};
    const if_exprt if_expr{b, address1, unknown_expr};
    const renamedt<exprt, L1> ptr1_l1 = state.rename<L1>(ptr1, ns);
    const renamedt<exprt, L1> if_expr_l1 = state.rename<L1>(if_expr, ns);
    // ptr1 <- b ? &value1 : unknown
    value_set.assign(ptr1_l1.get(), if_expr_l1.get(), ns, false, false);

    WHEN("Evaluating ptr1 == &value1")
    {
      const equal_exprt comparison{ptr1, address1};
      const renamedt<exprt, L2> renamed_comparison =
        state.rename(comparison, ns);
      auto result = try_evaluate_pointer_comparisons(
        renamed_comparison, value_set, ID_java, ns);
      THEN("Evaluation leaves the expression unchanged")
      {
        REQUIRE(result.get() == renamed_comparison.get());
      }
    }

    WHEN("Evaluating ptr1 != &value1")
    {
      const notequal_exprt comparison{ptr1, address1};
      const renamedt<exprt, L2> renamed_comparison =
        state.rename(comparison, ns);
      auto result = try_evaluate_pointer_comparisons(
        renamed_comparison, value_set, ID_java, ns);
      THEN("Evaluation leaves the expression unchanged")
      {
        REQUIRE(result.get() == renamed_comparison.get());
      }
    }

    WHEN("Evaluating ptr1 != nullptr")
    {
      const notequal_exprt comparison{ptr1, null_ptr};
      const renamedt<exprt, L2> renamed_comparison =
        state.rename(comparison, ns);
      auto result = try_evaluate_pointer_comparisons(
        renamed_comparison, value_set, ID_java, ns);
      THEN("Evaluation leaves the expression unchanged")
      {
        REQUIRE(result.get() == renamed_comparison.get());
      }
    }
  }

  GIVEN("A struct whose first element can only point to `&value1`")
  {
    // member is `struct_symbol.pointer_field`
    const member_exprt member = [&]() {
      std::vector<struct_typet::componentt> components;
      components.emplace_back("pointer_field", ptr_type);
      const struct_typet struct_type{components};
      const symbol_exprt struct_symbol{"struct_symbol", struct_type};
      add_to_symbol_table(symbol_table, struct_symbol);
      return member_exprt{struct_symbol, components.back()};
    }();

    value_sett value_set;
    const renamedt<exprt, L1> member_l1 = state.rename<L1>(member, ns);
    const renamedt<exprt, L1> address1_l1 = state.rename<L1>(address1, ns);

    // struct_symbol..pointer_field <- &value1
    {
      field_sensitivityt field_sensitivity{
        DEFAULT_MAX_FIELD_SENSITIVITY_ARRAY_SIZE};
      const exprt index_fs =
        field_sensitivity.apply(ns, state, member_l1.get(), true);
      value_set.assign(index_fs, address1_l1.get(), ns, false, false);
    }

    WHEN("Evaluating struct_symbol.pointer_field == &value1")
    {
      const equal_exprt comparison{member, address1};
      const renamedt<exprt, L2> renamed_comparison =
        state.rename(comparison, ns);
      auto result = try_evaluate_pointer_comparisons(
        renamed_comparison, value_set, ID_java, ns);
      THEN("Evaluation succeeds")
      {
        REQUIRE(result.get() == true_exprt{});
      }
    }

    WHEN("Evaluating struct_symbol.pointer_field == &value2")
    {
      const equal_exprt comparison{member, address2};
      const renamedt<exprt, L2> renamed_comparison =
        state.rename(comparison, ns);
      auto result = try_evaluate_pointer_comparisons(
        renamed_comparison, value_set, ID_java, ns);
      THEN("Evaluation succeeds")
      {
        REQUIRE(result.get() == false_exprt{});
      }
    }
  }
}
