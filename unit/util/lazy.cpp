/*******************************************************************\

Module: Unit tests for lazy

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <util/lazy.h>

SCENARIO("lazyt::from_fun test", "[core][util][lazy]")
{
  std::size_t call_counter = 0;
  auto length_with_counter = [&call_counter](const std::string &s) {
    ++call_counter;
    return s.length();
  };
  auto lazy_length =
    lazyt<int>::from_fun([&]() { return length_with_counter("foo"); });

  REQUIRE(call_counter == 0);
  auto result = lazy_length.force();
  REQUIRE(call_counter == 1);
  REQUIRE(result == 3);
  result = lazy_length.force();
  REQUIRE(call_counter == 1);
  REQUIRE(result == 3);
}

SCENARIO("lazy test", "[core][util][lazy]")
{
  std::size_t call_counter = 0;
  auto length_with_counter = [&call_counter](const std::string &s) {
    ++call_counter;
    return s.length();
  };
  lazyt<std::size_t> lazy_length =
    lazy([&] { return length_with_counter("foobar"); });

  REQUIRE(call_counter == 0);
  auto result = lazy_length.force();
  REQUIRE(call_counter == 1);
  REQUIRE(result == 6);
  result = lazy_length.force();
  REQUIRE(call_counter == 1);
  REQUIRE(result == 6);
}
