/*******************************************************************\

 Module: nonstd::optional unit tests

 Author: Diffblue Limited. All rights reserved.

\*******************************************************************/

#include "catch.hpp"
#include <util/optional.h>

TEST_CASE("Optional without a value", "[core][util][optional]")
{
  optionalt<bool> maybe_value;
  REQUIRE(maybe_value.has_value()==false);
  REQUIRE_THROWS_AS(maybe_value.value(), bad_optional_accesst);
}

TEST_CASE("Optional with a value", "[core][util][optional]")
{
  optionalt<bool> maybe_value=false;
  REQUIRE(maybe_value.has_value());
  REQUIRE(maybe_value.value()==false);
}


TEST_CASE("Optional with a value (operator access)", "[core][util][optional]")
{
  optionalt<bool> maybe_value=true;
  REQUIRE(maybe_value.has_value());
  REQUIRE(*maybe_value==true);
}
