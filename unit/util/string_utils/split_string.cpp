/*
  Author: Diffblue Ltd.
*/

/// \file
/// split_string Unit Tests

#include <testing-utils/catch.hpp>
#include <util/string_utils.h>

SCENARIO("split_string", "[core][utils][string_utils][split_string]")
{
  GIVEN("A non whitespace delimited string with two elements")
  {
    const char delimiter = ',';
    const std::string string = " a,, x , ,";

    WHEN("Not stripping, not removing empty")
    {
      std::vector<std::string> result;
      split_string(string, delimiter, result, false, false);

      THEN("All the elements should remain")
      {
        std::vector<std::string> expected_result = {" a", "", " x ", " ", ""};
        REQUIRE_THAT(
          result,
          Catch::Matchers::Vector::EqualsMatcher<std::string>{expected_result});
      }
    }
    WHEN("Stripping, not removing empty")
    {
      std::vector<std::string> result;
      split_string(string, delimiter, result, true, false);

      THEN("All whitespace borders should be removed but all elements remain")
      {
        std::vector<std::string> expected_result = {"a", "", "x", "", ""};
        REQUIRE_THAT(
          result,
          Catch::Matchers::Vector::EqualsMatcher<std::string>{expected_result});
      }
    }
    WHEN("Not stripping, removing empty")
    {
      std::vector<std::string> result;
      split_string(string, delimiter, result, false, true);

      THEN("All empty elements should be removed")
      {
        std::vector<std::string> expected_result = {" a", " x ", " "};
        REQUIRE_THAT(
          result,
          Catch::Matchers::Vector::EqualsMatcher<std::string>{expected_result});
      }
    }
    WHEN("Stripping and removing empty")
    {
      std::vector<std::string> result;
      split_string(string, delimiter, result, true, true);

      THEN("Should get the two parts in the vector")
      {
        std::vector<std::string> expected_result = {"a", "x"};
        REQUIRE_THAT(
          result,
          Catch::Matchers::Vector::EqualsMatcher<std::string>{expected_result});
      }
    }
  }
}

SCENARIO("split_string into two", "[core][utils][string_utils][split_string]")
{
  GIVEN("A string with one separator")
  {
    const char separator = ':';
    std::string string = "a:b";

    WHEN("Splitting into two strings")
    {
      std::string s1;
      std::string s2;
      split_string(string, separator, s1, s2, false);
      THEN("The string should be split")
      {
        REQUIRE(s1 == "a");
        REQUIRE(s2 == "b");
      }
    }
  }
}
