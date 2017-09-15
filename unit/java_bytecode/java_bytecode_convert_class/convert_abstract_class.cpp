/*******************************************************************\

 Module: Unit tests for converting abstract classes

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <catch.hpp>

#include <istream>
#include <memory>

#include <util/config.h>
#include <util/language.h>
#include <util/message.h>
#include <java_bytecode/java_bytecode_language.h>

SCENARIO("java_bytecode_convert_abstract_class",
  "[core][java_bytecode][java_bytecode_convert_class]")
{
  std::unique_ptr<languaget>java_lang(new_java_bytecode_language());

  // Configure the path loading
  cmdlinet command_line;
  command_line.set(
    "java-cp-include-files",
    "./java_bytecode/java_bytecode_convert_class");
  config.java.classpath.push_back(
    "./java_bytecode/java_bytecode_convert_class");

  // Configure the language
  null_message_handlert message_handler;
  java_lang->get_language_options(command_line);
  java_lang->set_message_handler(message_handler);

  std::istringstream java_code_stream("ignored");

  GIVEN("Some class files in the class path")
  {
    WHEN("Parsing an interface")
    {
      java_lang->parse(java_code_stream, "I.class");

      symbol_tablet new_symbol_table;
      java_lang->typecheck(new_symbol_table, "");

      java_lang->final(new_symbol_table);

      REQUIRE(new_symbol_table.has_symbol("java::I"));
      THEN("The symbol type should be abstract")
      {
        const symbolt &class_symbol=new_symbol_table.lookup("java::I");
        const typet &symbol_type=class_symbol.type;

        REQUIRE(symbol_type.id()==ID_struct);
        class_typet class_type=to_class_type(symbol_type);
        REQUIRE(class_type.is_class());
        REQUIRE(class_type.is_abstract());
      }
    }
    WHEN("Parsing an abstract class")
    {
      java_lang->parse(java_code_stream, "A.class");

      symbol_tablet new_symbol_table;
      java_lang->typecheck(new_symbol_table, "");

      java_lang->final(new_symbol_table);

      REQUIRE(new_symbol_table.has_symbol("java::A"));
      THEN("The symbol type should be abstract")
      {
        const symbolt &class_symbol=new_symbol_table.lookup("java::A");
        const typet &symbol_type=class_symbol.type;

        REQUIRE(symbol_type.id()==ID_struct);
        class_typet class_type=to_class_type(symbol_type);
        REQUIRE(class_type.is_class());
        REQUIRE(class_type.is_abstract());
      }
    }
    WHEN("Passing a concrete class")
    {
      java_lang->parse(java_code_stream, "C.class");

      symbol_tablet new_symbol_table;
      java_lang->typecheck(new_symbol_table, "");

      java_lang->final(new_symbol_table);

      REQUIRE(new_symbol_table.has_symbol("java::C"));
      THEN("The symbol type should not be abstract")
      {
        const symbolt &class_symbol=new_symbol_table.lookup("java::C");
        const typet &symbol_type=class_symbol.type;

        REQUIRE(symbol_type.id()==ID_struct);
        class_typet class_type=to_class_type(symbol_type);
        REQUIRE(class_type.is_class());
        REQUIRE_FALSE(class_type.is_abstract());
      }
    }
    WHEN("Passing a concrete class that implements an interface")
    {
      java_lang->parse(java_code_stream, "Implementor.class");

      symbol_tablet new_symbol_table;
      java_lang->typecheck(new_symbol_table, "");

      java_lang->final(new_symbol_table);

      REQUIRE(new_symbol_table.has_symbol("java::Implementor"));
      THEN("The symbol type should not be abstract")
      {
        const symbolt &class_symbol=
          new_symbol_table.lookup("java::Implementor");
        const typet &symbol_type=class_symbol.type;

        REQUIRE(symbol_type.id()==ID_struct);
        class_typet class_type=to_class_type(symbol_type);
        REQUIRE(class_type.is_class());
        REQUIRE_FALSE(class_type.is_abstract());
      }
    }
    WHEN("Passing a concrete class that extends an abstract class")
    {
      java_lang->parse(java_code_stream, "Extendor.class");

      symbol_tablet new_symbol_table;
      java_lang->typecheck(new_symbol_table, "");

      java_lang->final(new_symbol_table);

      REQUIRE(new_symbol_table.has_symbol("java::Extendor"));
      THEN("The symbol type should not be abstract")
      {
        const symbolt &class_symbol=
          new_symbol_table.lookup("java::Extendor");
        const typet &symbol_type=class_symbol.type;

        REQUIRE(symbol_type.id()==ID_struct);
        class_typet class_type=to_class_type(symbol_type);
        REQUIRE(class_type.is_class());
        REQUIRE_FALSE(class_type.is_abstract());
      }
    }
  }
}
