/*
  Author: Diffblue Ltd.
*/

/// \file
/// split_string Unit Tests

#include <testing-utils/catch.hpp>
#include <util/string_utils.h>

struct expected_resultst
{
  std::vector<std::string> no_strip_no_remove;
  std::vector<std::string> strip_no_remove;
  std::vector<std::string> no_strip_remove_empty;
  std::vector<std::string> strip_remove_empty;
};

/// For a given string and delimiter, use the split_string function with all
/// the possible combinations of stripping whitespace and removing empty
/// elements.
/// \param string: The string to split
/// \param delimiter: The delimter to split on
/// \param expected_results: The results expected for each of the versions of
/// the method
void run_on_all_variants(
  std::string string,
  char delimiter,
  const expected_resultst &expected_results)
{
  WHEN("Not stripping, not removing empty")
  {
    std::vector<std::string> result;
    split_string(string, delimiter, result, false, false);

    THEN("Should get expected vector")
    {
      REQUIRE_THAT(
        result,
        // NOLINTNEXTLINE(whitespace/braces)
        Catch::Matchers::Vector::EqualsMatcher<std::string>{
          expected_results.no_strip_no_remove});
    }
  }
  WHEN("Not stripping, removing empty")
  {
    std::vector<std::string> result;
    split_string(string, delimiter, result, false, true);

    THEN("Should get expected vector")
    {
      REQUIRE_THAT(
        result,
        // NOLINTNEXTLINE(whitespace/braces)
        Catch::Matchers::Vector::EqualsMatcher<std::string>{
          expected_results.no_strip_remove_empty});
    }
  }
  WHEN("Stripping, not removing empty")
  {
    std::vector<std::string> result;
    split_string(string, delimiter, result, true, false);

    THEN("Should get expected vector")
    {
      REQUIRE_THAT(
        result,
        // NOLINTNEXTLINE(whitespace/braces)
        Catch::Matchers::Vector::EqualsMatcher<std::string>{
          expected_results.strip_no_remove});
    }
  }
  WHEN("Stripping and removing empty")
  {
    std::vector<std::string> result;
    split_string(string, delimiter, result, true, true);

    THEN("Should get expected vector")
    {
      REQUIRE_THAT(
        result,
        // NOLINTNEXTLINE(whitespace/braces)
        Catch::Matchers::Vector::EqualsMatcher<std::string>{
          expected_results.strip_remove_empty});
    }
  }
}

SCENARIO("split_string", "[core][utils][string_utils][split_string]")
{
  GIVEN("A non whitespace delimited string with two elements")
  {
    const char delimiter = ',';
    const std::string string = " a,, x , ,";

    expected_resultst expected_results;
    expected_results.no_strip_no_remove = {" a", "", " x ", " ", ""};
    expected_results.strip_no_remove = {"a", "", "x", "", ""};
    expected_results.no_strip_remove_empty = {" a", " x ", " "};
    expected_results.strip_remove_empty = {"a", "x"};

    run_on_all_variants(string, delimiter, expected_results);
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
