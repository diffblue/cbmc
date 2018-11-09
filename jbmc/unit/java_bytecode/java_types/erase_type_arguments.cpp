/*******************************************************************\

Module: Unit tests for java_types

Author: Diffblue Ltd.

\*******************************************************************/

#include <java_bytecode/java_types.h>
#include <testing-utils/use_catch.h>

SCENARIO("erase_type_arguments", "[core][java_types]")
{
  THEN(
    "erase_type_arguments should leave strings with no type arguments "
    "unaltered.")
  {
    const std::string testInput1 = "testString1";
    REQUIRE(erase_type_arguments(testInput1) == testInput1);
  }

  THEN("erase_type_arguments should remove a simple type argument")
  {
    REQUIRE(
      erase_type_arguments("testClassName<testTypeArgument>") ==
      "testClassName");
  }

  THEN(
    "erase_type_arguments should remove multiple type arguments in cases "
    "of nested classes")
  {
    REQUIRE(
      erase_type_arguments(
        "outerClass<testTypeArgument1>$"
        "innerClass<testTypeArgument2>") == "outerClass$innerClass");
  }

  THEN(
    "erase_type_arguments should remove type arguments which contain nested "
    "type arguments")
  {
    REQUIRE(
      erase_type_arguments(
        "outerClass<testTypeArgument1<testTypeArgument2>>") == "outerClass");
  }

  THEN(
    "erase_type_arguments should remove multiple type arguments which contain "
    "nested type arguments in cases of nested classes")
  {
    REQUIRE(
      erase_type_arguments(
        "outerClass<testTypeArgument1<testTypeArgument2>>$"
        "innerClass<testTypeArgument3<testTypeArgument4>>") ==
      "outerClass$innerClass");
  }

  THEN(
    "erase_type_arguments should throw an error if a type argument is "
    "unterminated")
  {
    REQUIRE_THROWS_AS(
      erase_type_arguments(
        "testClassName<testTypeArgument1<testTypeArgument2>"),
      unsupported_java_class_signature_exceptiont);
  }
}
