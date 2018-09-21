/*******************************************************************\

 Module: Unit tests for converting fields

 Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <java_bytecode/java_bytecode_convert_class.h>
#include <java_bytecode/java_bytecode_parse_tree.h>
#include <java_bytecode/java_types.h>
#include <testing-utils/catch.hpp>

SCENARIO(
  "java_bytecode_parse_field",
  "[core][java_bytecode][java_bytecode_parser]")
{
  GIVEN("Some class with final and non final fields")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "ClassWithFields", "./java_bytecode/java_bytecode_parser");

    WHEN("Parsing the class file structure")
    {
      THEN("The the final status of the classes fields should be correct.")
      {
        const symbolt &class_symbol =
          symbol_table.lookup_ref("java::ClassWithFields");
        const java_class_typet &java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_component("final1").get_is_final());
        REQUIRE(java_class.get_component("final2").get_is_final());
        REQUIRE(java_class.get_component("final3").get_is_final());
        REQUIRE(!java_class.get_component("nonFinal1").get_is_final());
        REQUIRE(!java_class.get_component("nonFinal1").get_is_final());
        REQUIRE(!java_class.get_component("nonFinal1").get_is_final());
      }
    }
  }
}
