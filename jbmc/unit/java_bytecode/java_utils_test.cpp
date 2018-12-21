/*******************************************************************\

Module: Unit tests for parsing generic classes

Author: Diffblue Ltd.

 Note: Created by fotis on 09/10/2017.

\*******************************************************************/

#include <string>
#include <vector>

#include <testing-utils/catch.hpp>

#include <java_bytecode/java_types.h>
#include <java_bytecode/java_utils.h>

SCENARIO("Test that the generic signature delimiter lookup works reliably",
         "[core][java_util_test]")
{
  GIVEN("Given the signatures of some generic classes")
  {
    std::vector<std::string> generic_sigs
      {
        // Valid inputs
        "List<Integer>",
        "HashMap<String, Integer>",
        "List<List<Int>>",
        "List<List<List<Int>>>",
        // Invalid inputs
        "<",
        "List<Integer",
        "List<List<Integer>",
      };

    WHEN("We check if the closing tag is recognised correctly")
    {
      // TEST VALID CASES

      // List<Integer>
      REQUIRE(find_closing_delimiter(generic_sigs[0], 4, '<', '>')==12);
      // HashMap<String, Integer>
      REQUIRE(find_closing_delimiter(generic_sigs[1], 7, '<', '>')==23);
      // List<List<Int>>
      REQUIRE(find_closing_delimiter(generic_sigs[2], 4, '<', '>')==14);
      REQUIRE(find_closing_delimiter(generic_sigs[2], 9, '<', '>')==13);
      // List<List<List<Int>>>
      REQUIRE(find_closing_delimiter(generic_sigs[3], 14, '<', '>')==18);

      // TEST INVALID CASES

      // <
      REQUIRE(find_closing_delimiter(generic_sigs[4], 0, '<', '>')
              ==std::string::npos);
      // List<Integer
      REQUIRE(find_closing_delimiter(generic_sigs[5], 4, '<', '>')
              ==std::string::npos);
      // List<List<Integer>
      // (make sure that we still recognise the first delimiter correctly)
      REQUIRE(find_closing_delimiter(generic_sigs[6], 4, '<', '>')
              ==std::string::npos);
      REQUIRE(find_closing_delimiter(generic_sigs[6], 9, '<', '>')==17);
    }
  }
  GIVEN("Some bracketed functions")
  {
    std::vector<std::string> bracket_sigs{
      // Valid inputs
      "(Entry)",
      "Something(Else)",
      "(Nested(Bracket))",
      // Invalid inputs
      "(",
      "(Integer>",
    };
    WHEN("We check if the closing tag is recognised correctly")
    {
      // TEST VALID CASES

      // (Entry)
      REQUIRE(find_closing_delimiter(bracket_sigs[0], 0, '(', ')') == 6);
      // Something(Else)
      REQUIRE(find_closing_delimiter(bracket_sigs[1], 9, '(', ')') == 14);
      // (Nested(Bracket))
      REQUIRE(find_closing_delimiter(bracket_sigs[2], 0, '(', ')') == 16);
      REQUIRE(find_closing_delimiter(bracket_sigs[2], 7, '(', ')') == 15);

      // TEST INVALID CASES

      // (
      REQUIRE(
        find_closing_delimiter(bracket_sigs[3], 0, '(', ')') ==
        std::string::npos);
      // (Integer>
      REQUIRE(
        find_closing_delimiter(bracket_sigs[4], 0, '(', ')') ==
        std::string::npos);
    }
  }
}

SCENARIO("gather_full_class_name")
{
  GIVEN("Descriptor: class")
  {
    std::string descriptor = "LClassName;";
    THEN("Should get ClassName back")
    {
      const std::string &class_name = gather_full_class_name(descriptor);
      REQUIRE(class_name == "ClassName");
    }
  }
  GIVEN("Descriptor: A packaged class")
  {
    std::string descriptor = "Ljava/lang/Object;";
    THEN("Should get java.lang.Object back")
    {
      const std::string &class_name = gather_full_class_name(descriptor);
      REQUIRE(class_name == "java.lang.Object");
    }
  }
  GIVEN("Descriptor: A inner class")
  {
    std::string descriptor = "LOuter$Inner;";
    THEN("Should get Outer$Inner")
    {
      const std::string &class_name = gather_full_class_name(descriptor);
      REQUIRE(class_name == "Outer$Inner");
    }
  }
  GIVEN("Descriptor: a doubly nested inner class")
  {
    std::string descriptor = "LOuter$Inner$Inner2;";
    THEN("Should get Outer$Inner$Inner2")
    {
      const std::string &class_name = gather_full_class_name(descriptor);
      REQUIRE(class_name == "Outer$Inner$Inner2");
    }
  }

  GIVEN("Signature: An generic class")
  {
    std::string signature = "LClassName<TT;>;";
    THEN("Should get ClassName back")
    {
      const std::string &class_name = gather_full_class_name(signature);
      REQUIRE(class_name == "ClassName");
    }
  }
  GIVEN("Signature: An inner class in a generic class")
  {
    std::string signature = "LClassName<TT;>.Inner;";
    THEN("Should get ClassName$Inner back")
    {
      const std::string &class_name = gather_full_class_name(signature);
      REQUIRE(class_name == "ClassName$Inner");
    }
  }
  GIVEN("Signature: An generic inner class in a generic class")
  {
    std::string signature = "LClassName<TT;>.Inner<TV;>;";
    THEN("Should get ClassName$Inner back")
    {
      const std::string &class_name = gather_full_class_name(signature);
      REQUIRE(class_name == "ClassName$Inner");
    }
  }
  GIVEN("Signature: A generic inner class in a non generic class")
  {
    std::string signature = "LClassName.Inner<TV;>;";
    THEN("Should get ClassName$Inner back")
    {
      const std::string &class_name = gather_full_class_name(signature);
      REQUIRE(class_name == "ClassName$Inner");
    }
  }
  GIVEN(
    "Signature: A generic inner class in a non generic class in a non "
    "generic "
    "class")
  {
    std::string signature = "LClassName.Inner.Inner2<TT;>;";
    THEN("Should get ClassName$Inner$Inner2 back")
    {
      const std::string &class_name = gather_full_class_name(signature);
      REQUIRE(class_name == "ClassName$Inner$Inner2");
    }
  }
  GIVEN(
    "Signature: A generic inner class in a generic class in a non generic "
    "class")
  {
    std::string signature = "LClassName.Inner<UU;>.Inner2<TT;>;";
    THEN("Should get ClassName$Inner$Inner2 back")
    {
      const std::string &class_name = gather_full_class_name(signature);
      REQUIRE(class_name == "ClassName$Inner$Inner2");
    }
  }
  GIVEN(
    "Signature: A generic inner class in a generic class in a generic "
    "class")
  {
    std::string signature = "LClassName<TV;>.Inner<UU;>.Inner2<TT;>;";
    THEN("Should get ClassName$Inner$Inner2 back")
    {
      const std::string &class_name = gather_full_class_name(signature);
      REQUIRE(class_name == "ClassName$Inner$Inner2");
    }
  }
  GIVEN(
    "Signature: A non-generic inner class in a generic class in a non "
    "generic "
    "class")
  {
    std::string signature = "LClassName.Inner<UU;>.Inner2;";
    THEN("Should get ClassName$Inner$Inner2 back")
    {
      const std::string &class_name = gather_full_class_name(signature);
      REQUIRE(class_name == "ClassName$Inner$Inner2");
    }
  }
  GIVEN(
    "Signature: A non-generic inner class in a generic class in a generic "
    "class")
  {
    std::string signature = "LClassName<TV;>.Inner<UU;>.Inner2;";
    THEN("Should get ClassName$Inner$Inner2 back")
    {
      const std::string &class_name = gather_full_class_name(signature);
      REQUIRE(class_name == "ClassName$Inner$Inner2");
    }
  }
  GIVEN(
    "Signature: A non-generic inner class in a non-generic class in a "
    "generic "
    "class")
  {
    std::string signature = "LClassName<TV;>.Inner.Inner2;";
    THEN("Should get ClassName$Inner$Inner2 back")
    {
      const std::string &class_name = gather_full_class_name(signature);
      REQUIRE(class_name == "ClassName$Inner$Inner2");
    }
  }
  GIVEN(
    "Signature: A generic inner class in a non-generic class in a generic "
    "class")
  {
    std::string signature = "LClassName<TV;>.Inner.Inner2<TT;>;";
    THEN("Should get ClassName$Inner$Inner2 back")
    {
      const std::string &class_name = gather_full_class_name(signature);
      REQUIRE(class_name == "ClassName$Inner$Inner2");
    }
  }
}

SCENARIO("find_closing_semi_colon_for_reference_type", "[core][java_util_test]")
{
  GIVEN("A simple reference type")
  {
    std::string descriptor = "LA;";
    //                        |
    //                      012
    REQUIRE(find_closing_semi_colon_for_reference_type(descriptor, 0) == 2);
  }
  GIVEN("A generic reference type")
  {
    std::string descriptor = "LA<TT;>;";
    //                             |
    //                      01234567
    REQUIRE(find_closing_semi_colon_for_reference_type(descriptor, 0) == 7);
  }
  GIVEN("A generic reference type with multiple generic params")
  {
    std::string descriptor = "LA<TT;TU;>;";
    //                                |
    //                      01234567890
    REQUIRE(find_closing_semi_colon_for_reference_type(descriptor, 0) == 10);
  }
  GIVEN("A descriptor with multiple reference type")
  {
    std::string descriptor = "LA;LB;";
    //                        |
    //                      012
    REQUIRE(find_closing_semi_colon_for_reference_type(descriptor, 0) == 2);
  }
  GIVEN("A descriptor with multiple reference types parsing the second")
  {
    std::string descriptor = "LA;LB;";
    //                         | |
    //                      012345
    REQUIRE(find_closing_semi_colon_for_reference_type(descriptor, 3) == 5);
  }
  GIVEN("A descriptor inner class")
  {
    std::string descriptor = "LA$B;";
    //                          |
    //                      01234
    REQUIRE(find_closing_semi_colon_for_reference_type(descriptor, 0) == 4);
  }
  GIVEN("A signature inner class")
  {
    std::string descriptor = "LA.B;";
    //                          |
    //                      01234
    REQUIRE(find_closing_semi_colon_for_reference_type(descriptor, 0) == 4);
  }
  GIVEN("A inner class of a generic class")
  {
    std::string descriptor = "LA<TT;>.B;";
    //                               |
    //                      0123456789
    REQUIRE(find_closing_semi_colon_for_reference_type(descriptor, 0) == 9);
  }
  GIVEN("A inner class of a instantiated generic class")
  {
    std::string descriptor = "LA<LFoo;>.B;";
    //                                 |
    //                      012345678901
    REQUIRE(find_closing_semi_colon_for_reference_type(descriptor, 0) == 11);
  }
  GIVEN(
    "A signature with multiple references and an inner class of a generic "
    "class")
  {
    std::string descriptor = "LA<TT;>.B;LA<TT;>.B;";
    //                               |
    //                      0123456789
    REQUIRE(find_closing_semi_colon_for_reference_type(descriptor, 0) == 9);
  }
  GIVEN(
    "A signature with multiple references and an inner class of a generic "
    "class")
  {
    std::string descriptor = "LA<TT;>.B;LA<TT;>.B;";
    //                                |        |
    //                      01234567890123456789
    REQUIRE(find_closing_semi_colon_for_reference_type(descriptor, 10) == 19);
  }
}

SCENARIO("Test pretty printing auxiliary function", "[core][java_util_test]")
{
  using std::map;
  using std::string;

  WHEN("We have a series of cbmc internal java types")
  {
    // NOLINTNEXTLINE
    const map<string, string> types{
      // map<Input, Output>
      {"java::java.lang.Integer", "Integer"},
      {"java::CustomClass", "CustomClass"},
      {"java.lang.String", "String"},
      {"Hashmap", "Hashmap"},
      // We shouldn't prune types not imported in default import
      {"java.util.HashSet", "java.util.HashSet"}};

    THEN("We need to make sure that the types get pruned correctly.")
    {
      for(const auto &pair : types)
      {
        REQUIRE(pretty_print_java_type(pair.first) == pair.second);
      }
    }
  }
}
