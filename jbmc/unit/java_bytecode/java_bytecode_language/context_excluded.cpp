/*******************************************************************\

Module: Unit tests for java_bytecode_language.

Author: Diffblue Limited.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/symbol_table.h>

#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>

SCENARIO(
  "Exclude a method using context-include/exclude",
  "[core][java_bytecode][java_bytecode_language]")
{
  GIVEN("A class with all methods excluded except for main")
  {
    const symbol_tablet symbol_table =
      load_goto_model_from_java_class(
        "ClassWithDifferentModifiers",
        "./java_bytecode/java_bytecode_language",
        {},
        {{"context-include", "ClassWithDifferentModifiers.main"}})
        .get_symbol_table();

    WHEN("Converting the methods of this class")
    {
      const auto public_instance_symbol = symbol_table.lookup(
        "java::ClassWithDifferentModifiers.testPublicInstance:()I");
      REQUIRE(public_instance_symbol);
      const auto public_instance_type =
        type_try_dynamic_cast<java_method_typet>(public_instance_symbol->type);

      const auto private_static_symbol = symbol_table.lookup(
        "java::ClassWithDifferentModifiers.testPrivateStatic:()I");
      REQUIRE(private_static_symbol);
      const auto private_static_type =
        type_try_dynamic_cast<java_method_typet>(private_static_symbol->type);

      const auto protected_final_instance_symbol = symbol_table.lookup(
        "java::ClassWithDifferentModifiers.testProtectedFinalInstance:()I");
      REQUIRE(protected_final_instance_symbol);
      const auto protected_final_instance_type =
        type_try_dynamic_cast<java_method_typet>(
          protected_final_instance_symbol->type);

      const auto default_final_static_symbol = symbol_table.lookup(
        "java::ClassWithDifferentModifiers.testDefaultFinalStatic:()I");
      REQUIRE(default_final_static_symbol);
      const auto default_final_static_type =
        type_try_dynamic_cast<java_method_typet>(
          default_final_static_symbol->type);
      THEN(
        "Symbol values for excluded methods are nil as the lazy_goto_modelt "
        "for unit tests does not generate stub/exclude bodies.")
      {
        REQUIRE(public_instance_symbol->value.is_nil());
        REQUIRE(private_static_symbol->value.is_nil());
        REQUIRE(protected_final_instance_symbol->value.is_nil());
        REQUIRE(default_final_static_symbol->value.is_nil());
      }
      THEN(
        "Types of excluded methods are stored as java_method_typets in the "
        "symbol table.")
      {
        REQUIRE(public_instance_type);
        REQUIRE(private_static_type);
        REQUIRE(protected_final_instance_type);
        REQUIRE(default_final_static_type);
      }
      THEN("Access modifiers of excluded methods are preserved.")
      {
        REQUIRE(public_instance_type->get_access() == ID_public);
        REQUIRE(private_static_type->get_access() == ID_private);
        REQUIRE(protected_final_instance_type->get_access() == ID_protected);
        REQUIRE(default_final_static_type->get_access() == ID_default);
      }
      THEN("Static/Instance meta-information of excluded methods is preserved.")
      {
        REQUIRE_FALSE(public_instance_type->get_bool(ID_is_static));
        REQUIRE(private_static_type->get_bool(ID_is_static));
        REQUIRE_FALSE(protected_final_instance_type->get_bool(ID_is_static));
        REQUIRE(default_final_static_type->get_bool(ID_is_static));
      }
      THEN("Final/Non-final meta-information of excluded methods is preserved.")
      {
        REQUIRE_FALSE(public_instance_type->get_is_final());
        REQUIRE_FALSE(private_static_type->get_is_final());
        REQUIRE(protected_final_instance_type->get_is_final());
        REQUIRE(default_final_static_type->get_is_final());
      }
    }
  }
}
