/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: DiffBlue Limited. All rights reserved.

 Note: Created by fotis on 09/10/2017.

\*******************************************************************/

#include <string>
#include <vector>

#include <catch.hpp>

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
}
