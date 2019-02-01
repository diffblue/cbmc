/*******************************************************************\

Module: Unit tests of join_string

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// join_string Unit Tests

#include <sstream>
#include <string>
#include <vector>

#include <testing-utils/use_catch.h>
#include <util/string_utils.h>

TEST_CASE(
  "join_strings() should apply the function argument its passed to the "
  "elements of the container",
  "[core][utils][string_utils][join_strings]")
{
  std::vector<int> vec{1, 2, 3};
  auto result = join_strings(
                  std::ostringstream(),
                  vec.begin(),
                  vec.end(),
                  "-",
                  [](int x) { return std::to_string(x + 1); })
                  .str();
  REQUIRE(result == "2-3-4");
}

TEST_CASE(
  "join_strings() when passed no function argument should apply the default "
  "identity function to the elements of the container",
  "[core][utils][string_utils][join_strings]")
{
  std::vector<int> vec{1, 2, 3};
  auto result =
    join_strings(std::ostringstream(), vec.begin(), vec.end(), ",").str();
  REQUIRE(result == "1,2,3");
}
