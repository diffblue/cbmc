/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <catch.hpp>

#include <istream>
#include <memory>

#include <util/config.h>
#include <util/language.h>
#include <util/message.h>
#include <java_bytecode/java_bytecode_language.h>
#include <iostream>

SCENARIO(
  "java_bytecode_parse_derived_generic_class",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  std::unique_ptr<languaget> java_lang(new_java_bytecode_language());

  // Configure the path loading
  cmdlinet command_line;
  command_line.set(
    "java-cp-include-files",
    "./java_bytecode/java_bytecode_parse_generics");
  config.java.classpath.push_back(
    "./java_bytecode/java_bytecode_parse_generics");

  std::istringstream java_code_stream("ignored");
  null_message_handlert message_handler;

  // Configure the language, load the class files
  java_lang->get_language_options(command_line);
  java_lang->set_message_handler(message_handler);
  java_lang->parse(java_code_stream, "DerivedGeneric.class");
  symbol_tablet new_symbol_table;
  java_lang->typecheck(new_symbol_table, "");
  java_lang->final(new_symbol_table);

  THEN("There should be a symbol for the DerivedGenreic class")
  {
    std::string class_prefix="java::DerivedGeneric";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol=new_symbol_table.lookup(class_prefix);
    REQUIRE(derived_symbol.is_type);
    const typet &derived_type=derived_symbol.type;
    REQUIRE(derived_type.id()==ID_struct);
    const class_typet &class_type=to_class_type(derived_type);
    REQUIRE(class_type.is_class());
    REQUIRE_FALSE(class_type.get_bool(ID_incomplete_class));

    std::cout << class_type.pretty() << std::endl;

    // TODO(tkiley): Currently we do not support extracting information
    // about the base classes generic information.
  }
}
