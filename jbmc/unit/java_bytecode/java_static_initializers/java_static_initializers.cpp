/*******************************************************************\

Module: Unit tests for java_types

Author: Diffblue Ltd.

\*******************************************************************/

#include <java_bytecode/java_static_initializers.h>
#include <testing-utils/use_catch.h>

SCENARIO("is_clinit_function", "[core][java_static_initializers]")
{
  GIVEN("A function id that represents a clinit")
  THEN("is_clinit_function should return true.")
  {
    const std::string input = "com.something.package.TestClass.<clinit>:()V";
    REQUIRE(is_clinit_function(input));
  }
  GIVEN("A function id that does not represent a clinit")
  THEN("is_clinit_function should return false.")
  {
    const std::string input = "com.something.package.TestClass.<notclinit>:()V";
    REQUIRE_FALSE(is_clinit_function(input));
  }
}
