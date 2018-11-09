/*******************************************************************\

Module: Unit tests for converting abstract classes

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <istream>
#include <memory>

#include <util/config.h>
#include <util/message.h>

#include <java_bytecode/java_bytecode_language.h>

#include <java-testing-utils/load_java_class.h>

SCENARIO("java_bytecode_convert_abstract_class",
  "[core][java_bytecode][java_bytecode_convert_class]")
{
  GIVEN("Some class files in the class path")
  {
    WHEN("Parsing an interface")
    {
      const symbol_tablet &new_symbol_table=
        load_java_class("I", "./java_bytecode/java_bytecode_convert_class");

      THEN("The symbol type should be abstract")
      {
        const symbolt &class_symbol=*new_symbol_table.lookup("java::I");
        const typet &struct_tag_type = class_symbol.type;

        REQUIRE(struct_tag_type.id() == ID_struct);
        class_typet class_type = to_class_type(struct_tag_type);
        REQUIRE(class_type.is_class());
        REQUIRE(class_type.is_abstract());
      }
    }
    WHEN("Parsing an abstract class")
    {
      const symbol_tablet &new_symbol_table=
        load_java_class("A", "./java_bytecode/java_bytecode_convert_class");
      THEN("The symbol type should be abstract")
      {
        const symbolt &class_symbol=*new_symbol_table.lookup("java::A");
        const typet &struct_tag_type = class_symbol.type;

        REQUIRE(struct_tag_type.id() == ID_struct);
        class_typet class_type = to_class_type(struct_tag_type);
        REQUIRE(class_type.is_class());
        REQUIRE(class_type.is_abstract());
      }
    }
    WHEN("Passing a concrete class")
    {
      const symbol_tablet &new_symbol_table=
        load_java_class("C", "./java_bytecode/java_bytecode_convert_class");
      THEN("The symbol type should not be abstract")
      {
        const symbolt &class_symbol=*new_symbol_table.lookup("java::C");
        const typet &struct_tag_type = class_symbol.type;

        REQUIRE(struct_tag_type.id() == ID_struct);
        class_typet class_type = to_class_type(struct_tag_type);
        REQUIRE(class_type.is_class());
        REQUIRE_FALSE(class_type.is_abstract());
      }
    }
    WHEN("Passing a concrete class that implements an interface")
    {
      const symbol_tablet &new_symbol_table=
        load_java_class(
          "Implementor",
          "./java_bytecode/java_bytecode_convert_class");
      THEN("The symbol type should not be abstract")
      {
        const symbolt &class_symbol=
          *new_symbol_table.lookup("java::Implementor");
        const typet &struct_tag_type = class_symbol.type;

        REQUIRE(struct_tag_type.id() == ID_struct);
        class_typet class_type = to_class_type(struct_tag_type);
        REQUIRE(class_type.is_class());
        REQUIRE_FALSE(class_type.is_abstract());
      }
    }
    WHEN("Passing a concrete class that extends an abstract class")
    {
      const symbol_tablet &new_symbol_table=
        load_java_class(
          "Extender",
          "./java_bytecode/java_bytecode_convert_class");
      THEN("The symbol type should not be abstract")
      {
        const symbolt &class_symbol=
          *new_symbol_table.lookup("java::Extender");
        const typet &struct_tag_type = class_symbol.type;

        REQUIRE(struct_tag_type.id() == ID_struct);
        class_typet class_type = to_class_type(struct_tag_type);
        REQUIRE(class_type.is_class());
        REQUIRE_FALSE(class_type.is_abstract());
      }
    }
  }
}
