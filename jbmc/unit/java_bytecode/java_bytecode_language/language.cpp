/*******************************************************************\

Module: Unit tests for java_bytecode_language.

Author: Diffblue Limited.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/symbol_table.h>

#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>

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
        const struct_typet &opaque_class_struct =
          to_struct_type(opaque_class_symbol.type);
        const struct_union_typet::componentt &field =
          require_type::require_component(opaque_class_struct, "field2");
        REQUIRE(field.get_is_final());
      }
    }
  }
}
