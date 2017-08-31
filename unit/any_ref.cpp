/*******************************************************************\

Module: Any reference - type-safe wrapper around void*

Author: Diffblue Ltd.

\*******************************************************************/

#include "catch.hpp"
#include <util/any_ref.h>

TEST_CASE("Create and compare int reference")
{
  int variable=5;
  any_reft var_ref(variable);
  REQUIRE(var_ref.as<int>()==5);

  const int constant=5;
  any_reft const_ref(constant);
  REQUIRE(const_ref.as<const int>()==5);
}

TEST_CASE("Create and compare int non-assignable reference")
{
  int variable=5;
  const any_reft var_ref(variable);
  REQUIRE(var_ref.as<int>()==5);

  const int constant=5;
  const any_reft const_ref(constant);
  REQUIRE(const_ref.as<const int>()==5);
}

TEST_CASE("Allow conversion to const reference when original was non-const")
{
  const int value=5;
  any_reft ref(value);
  REQUIRE(ref.as<const int>()==5);
}

TEST_CASE("Conversion to a bad type should yield an error")
{
  const int value=7;
  any_reft ref(value);
  REQUIRE_THROWS_AS(ref.as<const bool>(), std::bad_cast);
}

TEST_CASE("Conversion to non-const if original was const should throw an error")
{
  const int value=7;
  any_reft ref(value);
  REQUIRE_THROWS_AS(ref.as<int>(), std::bad_cast);
}

TEST_CASE("any_ref should be assignable")
{
  const int value=7;
  any_reft ref(value);
  bool boolean=false;
  ref=boolean;
  REQUIRE(ref.as<const bool>()==false);
  ref.as<bool>()=true;
  REQUIRE(boolean==true);
}

class childt:public std::true_type { };

TEST_CASE("Conversion to base class is not allowed")
{
  childt child;
  any_reft ref(child);
  REQUIRE_THROWS_AS(ref.as<std::true_type>(), std::bad_cast);
}
