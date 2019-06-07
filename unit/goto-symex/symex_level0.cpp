/*******************************************************************\

Module: Unit tests for symex_target_equation::validate

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <goto-symex/goto_symex_state.h>
#include <goto-symex/renaming_level.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

SCENARIO("Level 0 renaming", "[core][goto-symex][symex-level0]")
{
  GIVEN(
    "A symbol table with a thread local variable, a shared variable, "
    "a guard, and a function")
  {
    symbol_tablet symbol_table;
    namespacet ns{symbol_table};
    const signedbv_typet int_type{32};

    const symbol_exprt symbol_nonshared{"nonShared", int_type};
    const ssa_exprt ssa_nonshared{symbol_nonshared};
    symbol_table.insert([&] {
      symbolt symbol;
      symbol.name = symbol_nonshared.get_identifier();
      symbol.type = symbol_nonshared.type();
      symbol.value = symbol_nonshared;
      symbol.is_thread_local = true;
      return symbol;
    }());

    const symbol_exprt symbol_shared{"shared", int_type};
    const ssa_exprt ssa_shared{symbol_shared};
    symbol_table.insert([&] {
      symbolt symbol;
      symbol.name = symbol_shared.get_identifier();
      symbol.type = symbol_shared.type();
      symbol.value = symbol_shared;
      symbol.is_thread_local = false;
      return symbol;
    }());

    const symbol_exprt symbol_guard{goto_symex_statet::guard_identifier(),
                                    bool_typet{}};
    const ssa_exprt ssa_guard{symbol_guard};
    symbol_table.insert([&] {
      symbolt symbol;
      symbol.name = symbol_guard.get_identifier();
      symbol.type = symbol_guard.type();
      symbol.value = symbol_guard;
      symbol.is_thread_local = false;
      return symbol;
    }());

    const code_typet code_type({}, int_type);
    const symbol_exprt symbol_fun{"fun", code_type};
    const ssa_exprt ssa_fun{symbol_fun};
    symbol_table.insert([&] {
      symbolt fun_symbol;
      fun_symbol.name = symbol_fun.get_identifier();
      fun_symbol.type = symbol_fun.type();
      fun_symbol.value = symbol_fun;
      fun_symbol.is_thread_local = true;
      return fun_symbol;
    }());

    WHEN("The non-shared symbol is renamed")
    {
      auto renamed = symex_level0(ssa_nonshared, ns, 423);

      THEN("Its L0 tag is set to the thread index")
      {
        REQUIRE(renamed.get().get_identifier() == "nonShared!423");
      }
    }

    WHEN("The shared symbol is renamed")
    {
      auto renamed = symex_level0(ssa_shared, ns, 423);

      THEN("Its L0 tag is unchanged")
      {
        REQUIRE(renamed.get().get_identifier() == "shared");
      }
    }

    WHEN("The guard is renamed")
    {
      auto renamed = symex_level0(ssa_guard, ns, 423);

      THEN("Its L0 tag is unchanged")
      {
        REQUIRE(
          renamed.get().get_identifier() ==
          goto_symex_statet::guard_identifier());
      }
    }

    WHEN("The function is renamed")
    {
      auto renamed = symex_level0(ssa_fun, ns, 423);

      THEN("Its L0 tag is unchanged")
      {
        REQUIRE(renamed.get().get_identifier() == "fun");
      }
    }
  }
}
