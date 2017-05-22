/*******************************************************************\

 Module: Example Catch Tests

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <catch.hpp>

unsigned int Factorial(unsigned int number)
{
  return number>1?Factorial(number-1)*number:1;
}

// This is an example unit test to demonstrate the build system and the
// catch unit test framework. The source code is taken from the documentation
// of catch.
TEST_CASE("Factorials are computed", "[core][factorial]")
{
  REQUIRE(Factorial(1)==1);
  REQUIRE(Factorial(2)==2);
  REQUIRE(Factorial(3)==6);
  REQUIRE(Factorial(10)==3628800);
}
