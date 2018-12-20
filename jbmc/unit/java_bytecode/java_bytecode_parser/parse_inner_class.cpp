/*******************************************************************\

 Module: Unit tests for converting inner classes

 Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <java_bytecode/java_types.h>
#include <testing-utils/catch.hpp>

#include <string>
#include <vector>

SCENARIO(
  "Parsing inner java classes",
  "[core][java_bytecode][java_bytecode_parser]")
{
  for(const auto &load_first : std::vector<std::string>{"Outer$Inner", "Outer"})
  {
    const symbol_tablet &symbol_table =
      load_java_class(load_first, "./java_bytecode/java_bytecode_parser");

    GIVEN("A class file of an inner class and " + load_first + " loaded first.")
    {
      WHEN("Parsing an inner class called \"Inner\".")
      {
        const symbolt *class_symbol = symbol_table.lookup("java::Outer$Inner");
        REQUIRE(class_symbol);
        const java_class_typet *class_type =
          type_try_dynamic_cast<java_class_typet>(class_symbol->type);
        REQUIRE(class_type);

        THEN("The inner class should have the name \"java::Outer$Inner\".")
        {
          REQUIRE(id2string(class_type->get_name()) == "java::Outer$Inner");
        }
        THEN("The inner class should have the inner name \"Inner\".")
        {
          REQUIRE(id2string(class_type->get_inner_name()) == "Inner");
        }
        THEN("The inner class is not considered to be an anonymous class.")
        {
          REQUIRE_FALSE(class_type->get_is_anonymous_class());
        }
        THEN("The inner class has the outer class \"Outer\".")
        {
          REQUIRE(id2string(class_type->get_outer_class()) == "Outer");
        }
      }
    }
    GIVEN(
      "A class file of a class which is not an inner class and " + load_first +
      " loaded first.")
    {
      WHEN("Parsing an outer class.")
      {
        const symbolt *class_symbol = symbol_table.lookup("java::Outer");
        REQUIRE(class_symbol);
        const java_class_typet *class_type =
          type_try_dynamic_cast<java_class_typet>(class_symbol->type);
        REQUIRE(class_type);

        THEN("The outer class should have the name \"java::Outer\".")
        {
          REQUIRE(id2string(class_type->get_name()) == "java::Outer");
        }
        THEN("The outer class should not have an inner name.")
        {
          REQUIRE(id2string(class_type->get_inner_name()).empty());
        }
        THEN("The outer class is not considered to be an anonymous class.")
        {
          REQUIRE_FALSE(class_type->get_is_anonymous_class());
        }
        THEN("The outer class does not have an outer class.")
        {
          REQUIRE(id2string(class_type->get_outer_class()).empty());
        }
      }
    }
    GIVEN(
      "A class file of an anonymous class and " + load_first + " loaded first.")
    {
      WHEN("Parsing an anonymous class.")
      {
        const symbolt *class_symbol = symbol_table.lookup("java::Outer$1");
        REQUIRE(class_symbol);
        const java_class_typet *class_type =
          type_try_dynamic_cast<java_class_typet>(class_symbol->type);
        REQUIRE(class_type);

        THEN("The anonymous class should have the name \"java::Outer$1\".")
        {
          REQUIRE(id2string(class_type->get_name()) == "java::Outer$1");
        }
        THEN("The anonymous class should not have an inner name.")
        {
          REQUIRE(id2string(class_type->get_inner_name()).empty());
        }
        THEN("The anonymous class is considered to be an anonymous class.")
        {
          REQUIRE(class_type->get_is_anonymous_class());
        }
        THEN("The anonymous class does not have an outer class.")
        {
          REQUIRE(id2string(class_type->get_outer_class()).empty());
        }
      }
    }
  }
  GIVEN("A class file of an outer class which is named with a '$'.")
  {
    WHEN("Parsing an outer class named with a '$'.")
    {
      const symbol_tablet &symbol_table = load_java_class(
        "Outer$RedHerring", "./java_bytecode/java_bytecode_parser");
      const auto *class_symbol = symbol_table.lookup("java::Outer$RedHerring");
      REQUIRE(class_symbol);
      const java_class_typet *class_type =
        type_try_dynamic_cast<java_class_typet>(class_symbol->type);
      REQUIRE(class_type);

      THEN("The outer class should have the name \"java::Outer$RedHerring\".")
      {
        REQUIRE(id2string(class_type->get_name()) == "java::Outer$RedHerring");
      }
      THEN("The outer class should not have an inner name.")
      {
        REQUIRE(id2string(class_type->get_inner_name()).empty());
      }
      THEN("The inner class is not considered to be an anonymous class.")
      {
        REQUIRE_FALSE(class_type->get_is_anonymous_class());
      }
      THEN("The outer class does not have an outer class.")
      {
        REQUIRE(id2string(class_type->get_outer_class()).empty());
      }
    }
  }
}
