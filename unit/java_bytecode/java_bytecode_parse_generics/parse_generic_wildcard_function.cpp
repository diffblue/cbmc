/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <catch.hpp>

#include <util/config.h>
#include <util/cmdline.h>
#include <util/language.h>
#include <util/prefix.h>

#include <java_bytecode/java_bytecode_language.h>

#include <iostream>

SCENARIO(
  "java_bytecode_parse_generic_wildcard",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  std::unique_ptr<languaget>java_lang(new_java_bytecode_language());

  // Configure the path loading
  cmdlinet command_line;
  command_line.set(
    "java-cp-include-files",
    "./java_bytecode/java_bytecode_parse_generics");
  config.java.classpath.push_back(
    "./java_bytecode/java_bytecode_parse_generics");

  std::istringstream java_code_stream("ignored");
  null_message_handlert message_handler;

  java_lang->get_language_options(command_line);
  java_lang->set_message_handler(message_handler);
  java_lang->parse(java_code_stream, "WildcardGenericFunctions.class");
  symbol_tablet new_symbol_table;
  java_lang->typecheck(new_symbol_table, "");
  java_lang->final(new_symbol_table);

  std::string class_prefix="java::WildcardGenericFunctions";

  // Validate loaded the java file
  REQUIRE(new_symbol_table.has_symbol(class_prefix));

  THEN("There should be a symbol for processSimpleGeneric")
  {
    const std::string func_name=".processSimpleGeneric";
    const std::string func_descriptor=":(LSimpleGeneric;)V";
    const std::string process_func_name=class_prefix+func_name+func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
  }

  THEN("There should be a symbol for processUpperBoundInterfaceGeneric")
  {
    const std::string func_name=".processUpperBoundInterfaceGeneric";
    const std::string func_descriptor=":(LSimpleGeneric;)V";
    const std::string process_func_name=class_prefix+func_name+func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
  }

  THEN("There should be a symbol for processUpperBoundClassGeneric")
  {
    const std::string func_name=".processUpperBoundClassGeneric";
    const std::string func_descriptor=":(LSimpleGeneric;)V";
    const std::string process_func_name=class_prefix+func_name+func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
  }

  THEN("There should be a symbol for processLowerBoundGeneric")
  {
    const std::string func_name=".processLowerBoundGeneric";
    const std::string func_descriptor=":(LSimpleGeneric;LFoo;)V";
    const std::string process_func_name=class_prefix+func_name+func_descriptor;

    REQUIRE(new_symbol_table.has_symbol(process_func_name));
  }
}
