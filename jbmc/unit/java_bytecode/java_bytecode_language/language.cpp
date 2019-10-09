/*******************************************************************\

Module: Unit tests for java_bytecode_language.

Author: Diffblue Limited.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/symbol_table.h>

#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>
#include <java_bytecode/java_bytecode_language.h>
#include <linking/static_lifetime_init.h>
#include <util/options.h>

SCENARIO(
  "java_bytecode_language_opaque_field",
  "[core][java_bytecode][java_bytecode_language]")
{
  GIVEN("A class that accesses opaque fields")
  {
    const symbol_tablet symbol_table = load_java_class(
      "ClassUsingOpaqueField", "./java_bytecode/java_bytecode_language");
    std::string opaque_class_prefix = "java::OpaqueClass";

    WHEN("When parsing opaque class with fields")
    {
      THEN("Static field field1 is marked as final")
      {
        const symbolt &opaque_field_symbol =
          symbol_table.lookup_ref(opaque_class_prefix + ".field1");
        REQUIRE(opaque_field_symbol.type.get_bool(ID_C_constant));
      }

      THEN("Non-static field field2 is marked final")
      {
        const symbolt &opaque_class_symbol =
          symbol_table.lookup_ref(opaque_class_prefix);
        const auto &opaque_class_struct =
          to_java_class_type(opaque_class_symbol.type);
        const auto &field =
          require_type::require_component(opaque_class_struct, "field2");
        REQUIRE(field.get_is_final());
      }
    }
  }
}

static void use_external_driver(java_bytecode_languaget &language)
{
  optionst options;
  options.set_option("symex-driven-lazy-loading", true);
  language.set_language_options(options);
}

SCENARIO(
  "LAZY_METHODS_MODE_EXTERNAL_DRIVER based generation of cprover_initialise",
  "[core][java_bytecode_language]")
{
  java_bytecode_languaget language;
  null_message_handlert null_message_handler;
  language.set_message_handler(null_message_handler);
  use_external_driver(language);
  symbol_tablet symbol_table;
  GIVEN("java_bytecode_languaget::typecheck is run.")
  {
    language.typecheck(symbol_table, "");
    THEN("The " INITIALIZE_FUNCTION " is in the symbol table without code.")
    {
      const symbolt *const initialise =
        symbol_table.lookup(INITIALIZE_FUNCTION);
      REQUIRE(initialise);
      REQUIRE(initialise->value.is_nil());
    }
    GIVEN(
      "java_bytecode_languaget::convert_lazy_method is used to "
      "generate " INITIALIZE_FUNCTION)
    {
      language.convert_lazy_method(INITIALIZE_FUNCTION, symbol_table);
      THEN("The " INITIALIZE_FUNCTION " is in the symbol table with code.")
      {
        const symbolt *const initialise =
          symbol_table.lookup(INITIALIZE_FUNCTION);
        REQUIRE(initialise);
        REQUIRE(can_cast_expr<codet>(initialise->value));
      }
    }
  }
}

TEST_CASE(
  "Standard generation of cprover_initialise",
  "[core][java_bytecode_language]")
{
  java_bytecode_languaget language;
  null_message_handlert null_message_handler;
  language.set_message_handler(null_message_handler);
  language.set_language_options(optionst{});
  symbol_tablet symbol_table;
  GIVEN("java_bytecode_languaget::typecheck is run.")
  {
    language.typecheck(symbol_table, "");
    THEN("The " INITIALIZE_FUNCTION
         " function is in the symbol table with code.")
    {
      const symbolt *const initialise =
        symbol_table.lookup(INITIALIZE_FUNCTION);
      REQUIRE(initialise);
      REQUIRE(can_cast_expr<codet>(initialise->value));
    }
  }
}
