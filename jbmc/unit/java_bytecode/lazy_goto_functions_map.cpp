/*******************************************************************\

Module: Unit tests for lazy_goto_functions_mapt

Author: Diffblue Ltd.

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/message.h>
#include <util/std_code.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_functions.h>

#include <java_bytecode/lazy_goto_functions_map.h>
#include <langapi/language_file.h>
#include <testing-utils/use_catch.h>

SCENARIO(
  "lazy_goto_functions_mapt::can_produce_function",
  "[core][java_bytecode][lazy_goto_functions_map]")
{
  // A map with no language files and a driver program that never generates a
  // body, so that the lazy-conversion and driver branches both return false.
  // can_produce_function can then only return true via the symbol-table
  // branch under test.
  std::map<irep_idt, goto_functiont> goto_functions;
  language_filest language_files;
  symbol_tablet symbol_table;
  null_message_handlert message_handler;

  lazy_goto_functions_mapt function_map{
    goto_functions,
    language_files,
    symbol_table,
    [](auto &&...) {},                      // post-process (unused here)
    [](const irep_idt &) { return false; }, // driver cannot generate a body
    [](auto &&...) { return false; },       // driver generate (unused here)
    message_handler};

  const code_typet code_type{{}, empty_typet{}};

  GIVEN("an entry already materialised in the symbol table with a body")
  {
    symbolt with_body;
    with_body.name = "with_body";
    with_body.type = code_type;
    with_body.value = code_blockt{}; // non-nil body
    symbol_table.add(with_body);

    THEN("can_produce_function returns true")
    {
      REQUIRE(function_map.can_produce_function("with_body"));
    }
  }

  GIVEN("a bodyless stub in the symbol table (code-typed, nil value)")
  {
    symbolt stub;
    stub.name = "stub";
    stub.type = code_type; // value left nil

    symbol_table.add(stub);

    THEN("can_produce_function returns false")
    {
      REQUIRE_FALSE(function_map.can_produce_function("stub"));
    }
  }

  GIVEN("a non-code symbol in the symbol table with a value")
  {
    symbolt data;
    data.name = "data";
    data.type = signedbv_typet{32};
    data.value = from_integer(0, data.type);

    symbol_table.add(data);

    THEN("can_produce_function returns false")
    {
      REQUIRE_FALSE(function_map.can_produce_function("data"));
    }
  }

  GIVEN("a function that is absent from the symbol table")
  {
    THEN("can_produce_function returns false")
    {
      REQUIRE_FALSE(function_map.can_produce_function("absent"));
    }
  }
}
