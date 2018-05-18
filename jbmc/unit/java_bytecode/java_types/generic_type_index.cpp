/*******************************************************************\

 Module: Unit tests for java_types

 Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java_bytecode/java_types.h>

SCENARIO("generic_type_index", "[core][java_types]")
{
  GIVEN("PrefixClassName<X, value> extends GenericClass<X,value>, "
          "and parameters X, value, Z")
  {
    const auto symbol_type = symbol_typet("java::GenericClass");
    const auto generic_symbol_type = java_generic_symbol_typet(
      symbol_type, "LGenericClass<TX;Tvalue;>;", "PrefixClassName");
    java_generic_parametert paramX(
      "PrefixClassName::X", symbol_typet(irep_idt()));
    java_generic_parametert value(
      "PrefixClassName::value", symbol_typet(irep_idt()));
    java_generic_parametert paramZ(
      "PrefixClassName::Z", symbol_typet(irep_idt()));

    WHEN("Looking for parameter indexes")
    {
      const auto indexX = generic_symbol_type.generic_type_index(paramX);
      const auto index_value = generic_symbol_type.generic_type_index(value);
      const auto indexZ = generic_symbol_type.generic_type_index(paramZ);

      THEN("X has index 0, Y index 1 and Z is not found")
      {
        REQUIRE(indexX.has_value());
        REQUIRE(indexX.value() == 0);
        REQUIRE(index_value.has_value());
        REQUIRE(index_value.value() == 1);
        REQUIRE_FALSE(indexZ.has_value());
      }
    }
  }

  GIVEN("HashMap<K,V> extends Map<K,V>, and parameters K, V, T")
  {
    const auto symbol_type = symbol_typet("java::java.util.Map");
    const auto generic_symbol_type = java_generic_symbol_typet(
      symbol_type, "Ljava/util/Map<TK;TV;>;", "java.util.HashMap");
    java_generic_parametert param0(
      "java.util.HashMap::K", symbol_typet(irep_idt()));
    java_generic_parametert param1(
      "java.util.HashMap::V", symbol_typet(irep_idt()));
    java_generic_parametert param2(
      "java.util.HashMap::T", symbol_typet(irep_idt()));

    WHEN("Looking for parameter indexes")
    {
      const auto index_param0 = generic_symbol_type.generic_type_index(param0);
      const auto index_param1 = generic_symbol_type.generic_type_index(param1);
      const auto index_param2 = generic_symbol_type.generic_type_index(param2);

      THEN("K has index 0, V index 1 and T is not found")
      {
        REQUIRE(index_param0.has_value());
        REQUIRE(index_param0.value() == 0);
        REQUIRE(index_param1.has_value());
        REQUIRE(index_param1.value() == 1);
        REQUIRE_FALSE(index_param2.has_value());
      }
    }
  }
}
