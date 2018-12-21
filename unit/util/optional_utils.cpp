/*******************************************************************\

Module: optional_utils unit tests

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/optional_utils.h>

#include <map>
#include <string>
#include <unordered_map>

namespace
{
template <typename map_like_collectiont>
void do_optional_lookup_test(map_like_collectiont &map)
{
  map.insert({"hello", "world"});
  map.insert({"pwd", "/home"});
  auto const hello_result = optional_lookup(map, "hello");
  REQUIRE(hello_result.has_value());
  REQUIRE(hello_result.value() == "world");
  auto const pwd_result = optional_lookup(map, "pwd");
  REQUIRE(pwd_result.has_value());
  REQUIRE(pwd_result.value() == "/home");
  REQUIRE_FALSE(optional_lookup(map, "does not exit").has_value());
}
} // namespace

TEST_CASE("Using optional_lookup with std::map")
{
  auto map = std::map<std::string, std::string>{};
  do_optional_lookup_test(map);
}

TEST_CASE("Using optional_lookup with std::unordered_map")
{
  auto map = std::unordered_map<std::string, std::string>{};
  do_optional_lookup_test(map);
}
