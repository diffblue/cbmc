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

SCENARIO("Level 1 renaming", "[core][goto-symex][symex-level1]")
{
  GIVEN("A symbol renamed to level 0, and a symex_level1t functor")
  {
    symbol_tablet symbol_table;
    namespacet ns{symbol_table};
    const signedbv_typet int_type{32};
    const symbol_exprt symbol_nonshared{"foo", int_type};
    ssa_exprt ssa{symbol_nonshared};
    symbol_table.insert([&] {
      symbolt symbol;
      symbol.name = symbol_nonshared.get_identifier();
      symbol.type = symbol_nonshared.type();
      symbol.value = symbol_nonshared;
      symbol.is_thread_local = true;
      return symbol;
    }());
    auto l0_symbol = symex_level0(ssa, ns, 50);
    symex_level1t symex_level1;

    WHEN("The symbol is not yet inserted in symex_level1")
    {
      THEN("Renaming leaves it unchanged")
      {
        REQUIRE(!symex_level1.has(l0_symbol));
        auto renamed = symex_level1(l0_symbol);
        REQUIRE(renamed.get().get_identifier() == "foo!50");
      }
    }

    WHEN("The symbol is inserted in symex_level1 several times")
    {
      symex_level1.insert(l0_symbol, 12134);
      THEN("The symbol is renamed to the index inserted")
      {
        REQUIRE(symex_level1.has(l0_symbol));
        auto renamed = symex_level1(l0_symbol);
        REQUIRE(renamed.get().get_identifier() == "foo!50@12134");
      }

      auto old = symex_level1.insert_or_replace(l0_symbol, 43950);
      THEN("insert_or_replace return the old value")
      {
        REQUIRE(old.has_value());
        REQUIRE(old->second == 12134);
      }
      THEN("The symbol is renamed to the new value")
      {
        auto renamed2 = symex_level1(l0_symbol);
        REQUIRE(renamed2.get().get_identifier() == "foo!50@43950");
      }
      REQUIRE(symex_level1.has(l0_symbol));
    }

    WHEN("insert_or_replace is called with a symbol not already inserted")
    {
      auto old = symex_level1.insert_or_replace(l0_symbol, 20051);
      THEN("insert_or_replace return an empty optional")
      {
        REQUIRE(!old.has_value());
      }
      THEN("The symbol is renamed to the index inserted")
      {
        REQUIRE(symex_level1.has(l0_symbol));
        auto renamed = symex_level1(l0_symbol);
        REQUIRE(renamed.get().get_identifier() == "foo!50@20051");
      }
    }
  }
}
