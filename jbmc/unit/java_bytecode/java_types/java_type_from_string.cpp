/*******************************************************************\

 Module: Unit tests for java_types

 Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java_bytecode/java_types.h>

SCENARIO("java_type_from_string", "[core][java_types]")
{
  // TODO : add more cases, the current test is not comprehensive

  GIVEN("Ljava/lang/Integer;")
  {
    const auto integer_type = java_type_from_string("Ljava/lang/Integer;", "");
    REQUIRE(integer_type != nil_typet());
  }

  GIVEN("TE;")
  {
    const auto generic_type_E = java_type_from_string("TE;", "MyClass");
    REQUIRE(generic_type_E != nil_typet());
  }

  GIVEN("Ljava/util/List<TX;>;")
  {
    const auto generic_list_type =
      java_type_from_string("Ljava/util/List<TX;>;", "java.util.List");
    REQUIRE(generic_list_type != nil_typet());
  }

  GIVEN("Ljava/util/List<Ljava/lang/Integer>;")
  {
    const auto integer_list_type =
      java_type_from_string("Ljava/util/List<Ljava/lang/Integer;>;", "");
    REQUIRE(integer_list_type != nil_typet());
  }

  GIVEN("Ljava/util/Map<TK;TV;>;")
  {
    const auto generic_struct_tag_type =
      java_type_from_string("Ljava/util/Map<TK;TV;>;", "java.util.Map");
    REQUIRE(generic_struct_tag_type != nil_typet());
  }
}
