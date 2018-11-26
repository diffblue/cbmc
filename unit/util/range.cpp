/*******************************************************************\

Module: Unit tests for range

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <vector>

#include <testing-utils/catch.hpp>
#include <util/range.h>

SCENARIO("range tests", "[core][util][range]")
{
  GIVEN("A vector with three strings")
  {
    std::vector<std::string> list;
    list.emplace_back("abc");
    list.emplace_back("cdef");
    list.emplace_back("acdef");
    auto range = make_range(list);
    std::size_t total_length = 0;
    THEN("Use range-for to compute the total length")
    {
      for(const auto &s : range)
        total_length += s.length();
      REQUIRE(total_length == 12);
    }
    THEN("Use map to compute individual lengths")
    {
      auto length_range = make_range(list).map<std::size_t>(
        [](const std::string &s) { return s.length(); });
      auto it = length_range.begin();
      REQUIRE(*it == 3);
      ++it;
      REQUIRE(*it == 4);
      ++it;
      REQUIRE(*it == 5);
      ++it;
      REQUIRE(it == length_range.end());
    }
    THEN("Filter using lengths")
    {
      auto filtered_range = make_range(list).filter(
        [&](const std::string &s) { return s.length() == 4; });
      auto it = filtered_range.begin();
      REQUIRE(*it == "cdef");
      ++it;
      REQUIRE(it == filtered_range.end());
    }
    THEN("Filter, map and use range-for on the same list")
    {
      auto range =
        make_range(list)
          .filter([&](const std::string &s) -> bool { return s[0] == 'a'; })
          .map<std::size_t>([&](const std::string &s) { return s.length(); });
      // Note that everything is performed on the fly, so none of the filter
      // and map functions have been computed yet, and no intermediary container
      // is created.
      std::size_t total = 0;
      for(const auto &l : range)
        total += l;
      REQUIRE(total == 8);
    }
  }
}
