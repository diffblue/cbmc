/*******************************************************************\

Module: Tests for coverage instrumentation config object and filters

Author: Diffblue Ltd

\*******************************************************************/

#include <goto-instrument/cover.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>
#include <util/options.h>
#include <util/symbol_table.h>
#include <util/ui_message.h>

namespace
{
symbolt create_new_symbol(const irep_idt &name, const irep_idt &file_name)
{
  symbolt symbol;
  symbol.name = name;
  source_locationt location;
  location.set_file(file_name);
  symbol.location = location;
  symbol.type = code_typet{{}, empty_typet{}};

  return symbol;
}
} // namespace

SCENARIO("get_cover_config is called", "[core]")
{
  symbol_tablet symbol_table;
  irep_idt id_Afoo = "java::A.foo";
  symbolt symbol_Afoo = create_new_symbol(id_Afoo, "A.java");

  symbolt symbol_Afoolish = create_new_symbol("java::A.foolish", "A.java");

  symbolt symbol_Bbar = create_new_symbol("java::B.bar", "B.java");

  symbolt symbol_Bbarbaric = create_new_symbol("java::B.barbaric", "B.java");

  symbolt symbol_A_Innerfoo = create_new_symbol("java::A$Inner.foo", "A.java");

  symbolt symbol_another_package_Afoo =
    create_new_symbol("java::another.package.A.foo", "another/package/A.java");

  symbol_table.insert(symbol_Afoo);
  symbol_table.insert(symbol_Afoolish);
  symbol_table.insert(symbol_Bbar);
  symbol_table.insert(symbol_Bbarbaric);

  goto_functiont dummy_function;

  ui_message_handlert message_handler(null_message_handler);

  GIVEN("cover-only set to an unrecognised value")
  {
    optionst options;
    options.set_option("cover-only", "diplodocus-with-a-duvet");

    WHEN("We give a valid main_symbol")
    {
      THEN("A config is not obtained")
      {
        try
        {
          get_cover_config(options, id_Afoo, symbol_table, message_handler);
          REQUIRE_FALSE(false);
        }
        catch(...)
        {
        }
      }
    }
  }

  GIVEN("cover-only set to 'file'")
  {
    optionst options;
    options.set_option("cover-only", "file");

    WHEN("We give a valid main_symbol")
    {
      auto ret =
        get_cover_config(options, id_Afoo, symbol_table, message_handler);

      THEN("A config is obtained that matches functions from the same file")
      {
        REQUIRE(ret.function_filters(symbol_Afoo, dummy_function));
        REQUIRE(ret.function_filters(symbol_Afoolish, dummy_function));
        REQUIRE_FALSE(ret.function_filters(symbol_Bbar, dummy_function));
        REQUIRE_FALSE(ret.function_filters(symbol_Bbarbaric, dummy_function));
        REQUIRE(ret.function_filters(symbol_A_Innerfoo, dummy_function));
        REQUIRE_FALSE(
          ret.function_filters(symbol_another_package_Afoo, dummy_function));
      }
    }
  }

  GIVEN("cover-only set to 'function'")
  {
    optionst options;
    options.set_option("cover-only", "function");

    WHEN("We give a valid main_symbol")
    {
      auto ret =
        get_cover_config(options, id_Afoo, symbol_table, message_handler);

      THEN("A config is obtained that matches the single function")
      {
        REQUIRE(ret.function_filters(symbol_Afoo, dummy_function));
        REQUIRE_FALSE(ret.function_filters(symbol_Afoolish, dummy_function));
        REQUIRE_FALSE(ret.function_filters(symbol_Bbar, dummy_function));
        REQUIRE_FALSE(ret.function_filters(symbol_Bbarbaric, dummy_function));
        REQUIRE_FALSE(ret.function_filters(symbol_A_Innerfoo, dummy_function));
        REQUIRE_FALSE(
          ret.function_filters(symbol_another_package_Afoo, dummy_function));
      }
    }
  }

  GIVEN("cover-only is not set")
  {
    optionst options;

    WHEN("We give a valid main_symbol")
    {
      auto ret =
        get_cover_config(options, id_Afoo, symbol_table, message_handler);

      THEN("A config is obtained that matches all the symbols")
      {
        REQUIRE(ret.function_filters(symbol_Afoo, dummy_function));
        REQUIRE(ret.function_filters(symbol_Afoolish, dummy_function));
        REQUIRE(ret.function_filters(symbol_Bbar, dummy_function));
        REQUIRE(ret.function_filters(symbol_Bbarbaric, dummy_function));
        REQUIRE(ret.function_filters(symbol_A_Innerfoo, dummy_function));
        REQUIRE(
          ret.function_filters(symbol_another_package_Afoo, dummy_function));
      }
    }

    WHEN("We give no main_symbol")
    {
      auto ret = get_cover_config(options, symbol_table, message_handler);

      THEN("A config is obtained that matches all the symbols")
      {
        REQUIRE(ret.function_filters(symbol_Afoo, dummy_function));
        REQUIRE(ret.function_filters(symbol_Afoolish, dummy_function));
        REQUIRE(ret.function_filters(symbol_Bbar, dummy_function));
        REQUIRE(ret.function_filters(symbol_Bbarbaric, dummy_function));
        REQUIRE(ret.function_filters(symbol_A_Innerfoo, dummy_function));
        REQUIRE(
          ret.function_filters(symbol_another_package_Afoo, dummy_function));
      }
    }
  }
}
