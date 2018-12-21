/*******************************************************************\

Module: Unit tests for parsing generic classes

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java-testing-utils/load_java_class.h>

SCENARIO(
  "parse_recursive_generic_class",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "RecursiveGeneric",
    "./java_bytecode/java_bytecode_parse_generics");

  std::string class_prefix = "java::RecursiveGeneric";

  REQUIRE(new_symbol_table.has_symbol(class_prefix));

  // TODO: Extend this unit test when recursive generic types are correctly
  // parsed - issue TG-1305
}
