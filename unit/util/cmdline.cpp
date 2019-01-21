/*******************************************************************\

Module: cmdlinet unit tests

Author: Diffblue Ltd.

\*******************************************************************/

#include <array>
#include <testing-utils/use_catch.h>
#include <util/cmdline.h>

TEST_CASE("cmdlinet::has_option", "[core][util][cmdline]")
{
  cmdlinet cmdline;
  REQUIRE(!cmdline.parse(0, nullptr, "(a)(b):"));
  REQUIRE(cmdline.has_option("a"));
  REQUIRE(cmdline.has_option("b"));
  REQUIRE(!cmdline.has_option("c"));
}

TEST_CASE("cmdline::option_names", "[core][util][cmdline]")
{
  cmdlinet cmdline;
  std::array<const char *, 5> args = {
    {"-f", "--a", "--b", "--c-with-arg", "c-arg"}};
  REQUIRE(!cmdline.parse(
    args.size(),
    args.data(),
    "?f"
    "(a)"
    "(b)"
    "(c-with-arg):"
    "(notset)"));
  auto option_names = std::vector<std::string>{};
  for(auto const &option_name : cmdline.option_names())
  {
    option_names.push_back(option_name);
  }
  REQUIRE(option_names.size() == 3);
  REQUIRE(option_names[0] == "a");
  REQUIRE(option_names[1] == "b");
  REQUIRE(option_names[2] == "c-with-arg");
  REQUIRE(cmdline.get_value(option_names[2].c_str()) == "c-arg");
}
