/*******************************************************************\

Module: Unit tests for java_types

Author: Diffblue Ltd.

\*******************************************************************/

#include <java_bytecode/java_types.h>
#include <testing-utils/use_catch.h>

SCENARIO("generic_type_index", "[core][java_types]")
{
  GIVEN("PrefixClassName<X, value> extends GenericClass<X,value>, "
          "and parameters X, value, Z")
  {
    const auto struct_tag_type = struct_tag_typet("java::GenericClass");
    const auto generic_struct_tag_type = java_generic_struct_tag_typet(
      struct_tag_type, "LGenericClass<TX;Tvalue;>;", "PrefixClassName");
    java_generic_parametert paramX(
      "PrefixClassName::X", struct_tag_typet(irep_idt()));
    java_generic_parametert value(
      "PrefixClassName::value", struct_tag_typet(irep_idt()));
    java_generic_parametert paramZ(
      "PrefixClassName::Z", struct_tag_typet(irep_idt()));

    WHEN("Looking for parameter indexes")
    {
      const auto indexX = generic_struct_tag_type.generic_type_index(paramX);
      const auto index_value =
        generic_struct_tag_type.generic_type_index(value);
      const auto indexZ = generic_struct_tag_type.generic_type_index(paramZ);

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
    const auto struct_tag_type = struct_tag_typet("java::java.util.Map");
    const auto generic_struct_tag_type = java_generic_struct_tag_typet(
      struct_tag_type, "Ljava/util/Map<TK;TV;>;", "java.util.HashMap");
    java_generic_parametert param0(
      "java.util.HashMap::K", struct_tag_typet(irep_idt()));
    java_generic_parametert param1(
      "java.util.HashMap::V", struct_tag_typet(irep_idt()));
    java_generic_parametert param2(
      "java.util.HashMap::T", struct_tag_typet(irep_idt()));

    WHEN("Looking for parameter indexes")
    {
      const auto index_param0 =
        generic_struct_tag_type.generic_type_index(param0);
      const auto index_param1 =
        generic_struct_tag_type.generic_type_index(param1);
      const auto index_param2 =
        generic_struct_tag_type.generic_type_index(param2);

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
