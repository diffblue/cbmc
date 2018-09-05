/*******************************************************************\

 Module: Unit tests for converting constructors and static initializers

 Author: Diffblue Limited.

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/symbol_table.h>

#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>

SCENARIO(
  "java_bytecode_convert_bridge_method",
  "[core][java_bytecode][java_bytecode_convert_method]")
{
  GIVEN("A class with a bridge method")
  {
    const symbol_tablet symbol_table = load_java_class(
      "ClassWithBridgeMethod", "./java_bytecode/java_bytecode_convert_method");

    const std::string method_name = "java::ClassWithBridgeMethod.compareTo";

    WHEN("When parsing the bridge method")
    {
      const symbolt function_symbol =
        symbol_table.lookup_ref(method_name + ":(Ljava/lang/Object;)I");

      const java_method_typet &function_type =
        require_type::require_java_method(function_symbol.type);
      THEN("The method symbol should be of java_method_typet")
      {
        REQUIRE(function_type.get_bool(ID_C_java_method_type));
      }
      THEN("And the method should be marked as a bridge method")
      {
        REQUIRE(function_type.get_bool(ID_is_bridge_method));
      }
    }
    WHEN("When parsing a non-bridge method")
    {
      THEN("THe method should not be marked as a bridge method")
      {
        const symbolt function_symbol =
          symbol_table.lookup_ref(method_name + ":(LClassWithBridgeMethod;)I");

        const java_method_typet &function_type =
          require_type::require_java_method(function_symbol.type);
        THEN("The method should be marked as a bridge method")
        {
          REQUIRE_FALSE(function_type.get_bool(ID_is_bridge_method));
        }
      }
    }
  }
}

SCENARIO(
  "java_bytecode_convert_final_method",
  "[core][java_bytecode][java_bytecode_convert_method]")
{
  GIVEN("A class with final and non-final methods")
  {
    const symbol_tablet symbol_table = load_java_class(
      "ClassWithFinalMethod", "./java_bytecode/java_bytecode_convert_method");

    WHEN("When parsing a final method")
    {
      const symbolt function_symbol =
        symbol_table.lookup_ref("java::ClassWithFinalMethod.finalFunc:()I");
      const java_method_typet &function_type =
        require_type::require_java_method(function_symbol.type);
      THEN("The method should be marked as final")
      {
        REQUIRE(function_type.get_is_final());
      }
    }
    WHEN("When parsing a non-final method")
    {
      const symbolt function_symbol =
        symbol_table.lookup_ref("java::ClassWithFinalMethod.nonFinalFunc:()I");
      const java_method_typet &function_type =
        require_type::require_java_method(function_symbol.type);
      THEN("The method should not be marked as final")
      {
        REQUIRE(!function_type.get_is_final());
      }
    }
    WHEN("When parsing an opaque method")
    {
      const symbolt function_symbol =
        symbol_table.lookup_ref("java::OpaqueClass.staticFunc:()I");
      const java_method_typet &function_type =
        require_type::require_java_method(function_symbol.type);
      THEN("The method should be marked as final")
      {
        REQUIRE(function_type.get_is_final());
      }
    }
  }
}
