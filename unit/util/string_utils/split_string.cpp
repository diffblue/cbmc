/*******************************************************************\

Module: Unit tests of split_string

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// split_string Unit Tests

#include <testing-utils/use_catch.h>
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
///   the method
void run_on_all_variants(
  std::string string,
  char delimiter,
  const expected_resultst &expected_results)
{
  WHEN("Not stripping, not removing empty")
  {
    std::vector<std::string> result =
      split_string(string, delimiter, false, false);

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
    std::vector<std::string> result =
      split_string(string, delimiter, false, true);

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
    std::vector<std::string> result =
      split_string(string, delimiter, true, false);

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
    std::vector<std::string> result =
    split_string(string, delimiter, true, true);

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
  GIVEN("An empty string")
  {
    std::string string = "";
    WHEN("Splitting it")
    {
      expected_resultst expected_results;
      expected_results.no_strip_no_remove = {""};
      expected_results.strip_no_remove = {""};

      // TODO(tkiley): This is probably wrong, since I'd expect removing empty
      // TODO(tkiley): elements to return an empty vector here.
      expected_results.no_strip_remove_empty = {""};
      expected_results.strip_remove_empty = {""};

      run_on_all_variants(string, ',', expected_results);
    }
  }
  GIVEN("A whitespace only string")
  {
    std::string string = "    ";
    WHEN("Splitting it")
    {
      expected_resultst expected_results;
      expected_results.no_strip_no_remove = {"    "};
      expected_results.strip_no_remove = {""};
      expected_results.no_strip_remove_empty = {"    "};
      // TODO(tkiley): This is probably wrong, since I'd expect removing empty
      // TODO(tkiley): elements to return an empty vector here.
      expected_results.strip_remove_empty = {""};

      run_on_all_variants(string, ',', expected_results);
    }
  }
  GIVEN("A whitespace delimter")
  {
    std::string string = "a\nb\nc";
    const char delimiter = '\n';

    WHEN("Not stripping, not removing empty")
    {
      std::vector<std::string> result =
        split_string(string, delimiter, false, false);

      THEN("Should get expected vector")
      {
        std::vector<std::string> expected_result = {"a", "b", "c"};
        REQUIRE_THAT(
          result,
          Catch::Matchers::Vector::EqualsMatcher<std::string>{expected_result});
      }
    }
    WHEN("Not stripping, removing empty")
    {
      std::vector<std::string> result =
        split_string(string, delimiter, false, true);

      THEN("Should get expected vector")
      {
        std::vector<std::string> expected_result = {"a", "b", "c"};
        REQUIRE_THAT(
          result,
          Catch::Matchers::Vector::EqualsMatcher<std::string>{expected_result});
      }
    }
    // TODO(tkiley): here we should check what happens when trying to enable
    // TODO(tkiley): strip, but currently the behaviour terminates the unit test
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
  GIVEN("A string and a whitespace delimiter")
  {
    std::string string = "a\nb";
    const char delimiter = '\n';

    WHEN("Splitting in two and not stripping")
    {
      std::string s1;
      std::string s2;
      split_string(string, delimiter, s1, s2, false);
      THEN("The string should be split")
      {
        REQUIRE(s1 == "a");
        REQUIRE(s2 == "b");
      }
    }
    // TODO(tkiley): here we should check what happens when trying to enable
    // TODO(tkiley): strip, but currently the behaviour terminates the unit test
  }
}
