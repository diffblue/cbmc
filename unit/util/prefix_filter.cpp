/*******************************************************************\

Module: Unit tests for prefix_filter

Author: Peter Schrammel

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/prefix_filter.h>

TEST_CASE("include all", "[core][util][prefix_filter]")
{
  prefix_filtert filter{{}, {}};
  REQUIRE(filter("abc"));
  REQUIRE(filter("bcd"));
  REQUIRE(filter("a"));
  REQUIRE(filter("z"));
  REQUIRE(filter("af"));
  REQUIRE(filter("y"));
}

TEST_CASE("include-only", "[core][util][prefix_filter]")
{
  prefix_filtert filter{{"ab", "bcd"}, {}};
  REQUIRE(filter("abc"));
  REQUIRE(filter("bcd"));
  REQUIRE_FALSE(filter("a"));
  REQUIRE_FALSE(filter("z"));
  REQUIRE_FALSE(filter("af"));
  REQUIRE_FALSE(filter("y"));
}

TEST_CASE("exclude from all", "[core][util][prefix_filter]")
{
  prefix_filtert filter{{}, {"ab", "bcd"}};
  REQUIRE_FALSE(filter("abc"));
  REQUIRE_FALSE(filter("bcd"));
  REQUIRE(filter("a"));
  REQUIRE(filter("z"));
  REQUIRE(filter("af"));
  REQUIRE(filter("y"));
}

TEST_CASE("exclude from include", "[core][util][prefix_filter]")
{
  prefix_filtert filter{{"a", "z"}, {"ab", "bcd"}};
  REQUIRE_FALSE(filter("abc"));
  REQUIRE_FALSE(filter("bcd"));
  REQUIRE(filter("a"));
  REQUIRE(filter("z"));
  REQUIRE(filter("af"));
  REQUIRE_FALSE(filter("y"));
}
