/*******************************************************************\

Module: Unit tests for java string literal generation.

Author: Diffblue Limited

\*******************************************************************/

#include <java_bytecode/java_entry_point.h>
#include <java_bytecode/java_string_literals.h>
#include <java_bytecode/java_types.h>
#include <java_bytecode/java_utils.h>
#include <linking/static_lifetime_init.h>
#include <testing-utils/invariant.h>
#include <testing-utils/use_catch.h>
#include <util/symbol_table.h>

TEST_CASE(
  "Test that java_string_literal can be used before " INITIALIZE_FUNCTION
  " is made but not afterwards.",
  "[core][java_bytecode][java_string_literals]")
{
  symbol_tablet symbol_table;
  null_message_handlert message_handler{};
  generate_class_stub("java.lang.Object", symbol_table, message_handler, {});
  generate_class_stub("java.lang.String", symbol_table, message_handler, {});
  REQUIRE(symbol_table.lookup(
    get_or_create_string_literal_symbol("foo", symbol_table, false)
      .get_identifier()));

  create_java_initialize(symbol_table);
  symbol_table.get_writeable_ref(INITIALIZE_FUNCTION).value = code_blockt{};
  const cbmc_invariants_should_throwt invariants_throw;
  REQUIRE_THROWS_MATCHES(
    get_or_create_string_literal_symbol("bar", symbol_table, false),
    invariant_failedt,
    invariant_failure_containing("Cannot create more string literals after "
                                 "making " INITIALIZE_FUNCTION));
}
