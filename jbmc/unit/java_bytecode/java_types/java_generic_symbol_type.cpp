/*******************************************************************\

 Module: Unit tests for java_types

 Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java_bytecode/java_types.h>

SCENARIO("java_generic_struct_tag_type", "[core][java_types]")
{
  GIVEN("LGenericClass<TX;TY;>;")
  {
    auto struct_tag_type = struct_tag_typet("java::GenericClass");
    const auto generic_struct_tag_type = java_generic_struct_tag_typet(
      struct_tag_type, "LGenericClass<TX;TY;>;", "PrefixClassName");

    REQUIRE(generic_struct_tag_type.get_identifier() == "java::GenericClass");

    auto types = generic_struct_tag_type.generic_types();
    REQUIRE(types.size() == 2);

    auto generic_var0 = to_java_generic_parameter(types[0]).type_variable();
    REQUIRE(generic_var0.get_identifier() == "PrefixClassName::X");

    auto generic_var1 = to_java_generic_parameter(types[1]).type_variable();
    REQUIRE(generic_var1.get_identifier() == "PrefixClassName::Y");
  }
}
