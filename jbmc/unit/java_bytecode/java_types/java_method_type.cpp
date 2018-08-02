/*******************************************************************\

 Module: Unit tests for java_types

 Author: Diffblue Ltd.

\*******************************************************************/

#include <java_bytecode/java_types.h>
#include <testing-utils/catch.hpp>

SCENARIO("java_method_type", "[core][java_types]")
{
  GIVEN("A code_typet")
  {
    code_typet::parameterst parameters;
    typet return_type;
    code_typet code_type = code_typet();
    THEN("It has id code_typet and not java_method_typet")
    {
      REQUIRE(code_type.id() == ID_code);
      REQUIRE_FALSE(code_type.get_bool(ID_C_java_method_type));
    }

    WHEN("It is converted to a java_method_typet")
    {
      THEN("It should have id code_typet and java_method_typet")
      {
        java_method_typet method_type = to_java_method_type(code_type);
        REQUIRE(method_type.id() == ID_code);
        REQUIRE(method_type.get_bool(ID_C_java_method_type));
      }
    }
  }
}
