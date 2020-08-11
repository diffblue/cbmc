/// \file
/// Unit tests of src/goto-cc/armcc_cmdline.cpp
/// \author Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <util/optional.h>

#include <string>
#include <vector>

optionalt<std::string>
prefix_in_list(const std::string &option, const std::vector<std::string> &list);

static const std::vector<std::string> test_list{"spam", "eggs", "and", "ham"};

TEST_CASE("prefix_in_list exact match", "[core][armcc_cmdline][prefix_in_list]")
{
  REQUIRE(*prefix_in_list("spam", test_list) == "spam");
  REQUIRE(*prefix_in_list("ham", test_list) == "ham");
}

TEST_CASE(
  "prefix_in_list match prefix",
  "[core][armcc_cmdline][prefix_in_list]")
{
  REQUIRE(*prefix_in_list("sp", test_list) == "spam");
  REQUIRE(*prefix_in_list("ha", test_list) == "ham");
}

TEST_CASE("prefix_in_list unmatched", "[core][armcc_cmdline][prefix_in_list]")
{
  REQUIRE_FALSE(prefix_in_list("foobar", test_list));
}
