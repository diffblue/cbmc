/*******************************************************************\

Module: Unit tests for converting annotations

Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <java_bytecode/java_bytecode_convert_class.h>
#include <java_bytecode/java_bytecode_parse_tree.h>
#include <java_bytecode/java_types.h>
#include <testing-utils/catch.hpp>

SCENARIO(
  "java_bytecode_parse_class",
  "[core][java_bytecode][java_bytecode_parser]")
{
  GIVEN("Some class with a class hierarchy")
  {
    const symbol_tablet &new_symbol_table =
      load_java_class("ChildClass", "./java_bytecode/java_bytecode_parser");
    WHEN("Parsing the class file structure")
    {
      THEN("We should be able to get the first super class")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::ChildClass");
        const java_class_typet &java_class =
          to_java_class_type(class_symbol.type);
        REQUIRE(java_class.get_super_class() == "ParentClass");
      }
      THEN("We should be able to get the second super class")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::ChildClass");
        const java_class_typet &java_class =
          to_java_class_type(class_symbol.type);
        const symbolt &class_symbol1 = new_symbol_table.lookup_ref(
          "java::" + id2string(java_class.get_super_class()));
        const java_class_typet &java_class1 =
          to_java_class_type(class_symbol1.type);
        REQUIRE(java_class1.get_super_class() == "GrandparentClass");
      }
      THEN("We should be able to get the third super class")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::ChildClass");
        const java_class_typet &java_class =
          to_java_class_type(class_symbol.type);
        const symbolt &class_symbol1 = new_symbol_table.lookup_ref(
          "java::" + id2string(java_class.get_super_class()));
        const java_class_typet &java_class1 =
          to_java_class_type(class_symbol1.type);
        const symbolt &class_symbol2 = new_symbol_table.lookup_ref(
          "java::" + id2string(java_class1.get_super_class()));
        const java_class_typet &java_class2 =
          to_java_class_type(class_symbol2.type);
        REQUIRE(java_class2.get_super_class() == "java.lang.Object");
      }
      THEN("We should be able to get the fourth super class")
      {
        const symbolt &class_symbol =
          new_symbol_table.lookup_ref("java::ChildClass");
        const java_class_typet &java_class =
          to_java_class_type(class_symbol.type);
        const symbolt &class_symbol1 = new_symbol_table.lookup_ref(
          "java::" + id2string(java_class.get_super_class()));
        const java_class_typet &java_class1 =
          to_java_class_type(class_symbol1.type);
        const symbolt &class_symbol2 = new_symbol_table.lookup_ref(
          "java::" + id2string(java_class1.get_super_class()));
        const java_class_typet &java_class2 =
          to_java_class_type(class_symbol2.type);
        const symbolt &class_symbol3 = new_symbol_table.lookup_ref(
          "java::" + id2string(java_class2.get_super_class()));
        const java_class_typet &java_class3 =
          to_java_class_type(class_symbol3.type);
        REQUIRE(java_class3.get_super_class().empty());
      }
    }
  }
}
