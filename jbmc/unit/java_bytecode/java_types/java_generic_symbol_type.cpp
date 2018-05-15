/*******************************************************************\

 Module: Unit tests for java_types

 Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java_bytecode/java_types.h>

SCENARIO("java_generic_symbol_type", "[core][java_types]")
{
  GIVEN("LGenericClass<TX;TY;>;")
  {
    auto symbol_type = symbol_typet("java::GenericClass");
    const auto generic_symbol_type = java_generic_symbol_typet(
      symbol_type, "LGenericClass<TX;TY;>;", "PrefixClassName");

    REQUIRE(generic_symbol_type.get_identifier() == "java::GenericClass");

    auto types = generic_symbol_type.generic_types();
    REQUIRE(types.size() == 2);

    auto generic_var0 = to_java_generic_parameter(types[0]).type_variable();
    REQUIRE(generic_var0.get_identifier() == "PrefixClassName::X");

    auto generic_var1 = to_java_generic_parameter(types[1]).type_variable();
    REQUIRE(generic_var1.get_identifier() == "PrefixClassName::Y");
  }
}
