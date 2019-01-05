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
    THEN("Use range-for to compute the total length")
    {
      auto range = make_range(list);
      std::size_t total_length = 0;
      for(const auto &s : range)
        total_length += s.length();
      REQUIRE(total_length == 12);
    }
    THEN("Use map to compute individual lengths")
    {
      auto length_range =
        make_range(list).map([](const std::string &s) { return s.length(); });
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
          .map([&](const std::string &s) { return s.length(); });
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

class move_onlyt
{
public:
  move_onlyt(move_onlyt &&) = default;
  move_onlyt &operator=(move_onlyt &&) = default;
  move_onlyt(const move_onlyt &) = delete;
  move_onlyt &operator=(const move_onlyt &) = delete;

  explicit move_onlyt(int value) : value{value} {};
  int value = 0;
};

bool is_odd(const move_onlyt &move_only)
{
  return move_only.value % 2 != 0;
}

const auto add = [](int left) {
  return [=](const move_onlyt &right) { return left + right.value; };
};

SCENARIO(
  "Range tests, with collections of move only typed values.",
  "[core][util][range]")
{
  GIVEN("A vector of move only typed values.")
  {
    std::vector<move_onlyt> input;
    for(int i = 1; i <= 10; ++i)
      input.emplace_back(i);
    THEN("Values from a range of made from the vector can be moved.")
    {
      auto input_range = make_range(input);
      move_onlyt destination{std::move(*input_range.begin())};
      REQUIRE(destination.value == 1);
    }
    THEN("A range of made from the vector can be filtered.")
    {
      auto odds_filter = make_range(input).filter(is_odd);
      const std::size_t total =
        std::distance(odds_filter.begin(), odds_filter.end());
      REQUIRE(total == 5);
      auto iterator = odds_filter.begin();
      REQUIRE((iterator++)->value == 1);
      REQUIRE((iterator++)->value == 3);
      REQUIRE((iterator++)->value == 5);
      REQUIRE((iterator++)->value == 7);
      REQUIRE((iterator++)->value == 9);
    }
    THEN("Values from a filtered range made from the vector can be moved.")
    {
      std::vector<move_onlyt> odds;
      for(move_onlyt &odd : make_range(input).filter(is_odd))
        odds.emplace_back(std::move(odd));

      REQUIRE(odds.size() == 5);
      REQUIRE(odds[0].value == 1);
      REQUIRE(odds[1].value == 3);
      REQUIRE(odds[2].value == 5);
      REQUIRE(odds[3].value == 7);
      REQUIRE(odds[4].value == 9);
    }
    THEN("Map can be applied to a range of move only typed values.")
    {
      std::vector<int> results;
      for(int result : make_range(input).map(add(1)))
        results.push_back(result);

      const std::vector<int> expected_results{2, 3, 4, 5, 6, 7, 8, 9, 10, 11};
      REQUIRE(results == expected_results);
    }
  }
  GIVEN("Two vectors containing move only types values.")
  {
    std::vector<move_onlyt> input1;
    for(int i = 1; i <= 3; ++i)
      input1.emplace_back(i);
    std::vector<move_onlyt> input2;
    for(int i = 7; i <= 9; ++i)
      input2.emplace_back(i);

    THEN("Values from concatenated ranges made from the vector can be moved.")
    {
      std::vector<move_onlyt> both_inputs;
      for(move_onlyt &input : make_range(input1).concat(make_range(input2)))
        both_inputs.emplace_back(std::move(input));

      REQUIRE(both_inputs.size() == 6);
      REQUIRE(both_inputs[0].value == 1);
      REQUIRE(both_inputs[1].value == 2);
      REQUIRE(both_inputs[2].value == 3);
      REQUIRE(both_inputs[3].value == 7);
      REQUIRE(both_inputs[4].value == 8);
      REQUIRE(both_inputs[5].value == 9);
    }
  }
  GIVEN("A const vector of ints.")
  {
    const std::vector<int> input{1, 2, 3, 4, 5};

    THEN("The vector can be mapped into a range of move-only types")
    {
      std::vector<move_onlyt> results;
      const auto make_move_only = [](int i) { return move_onlyt{i}; };
      for(auto &incremented : make_range(input).map(make_move_only))
        results.emplace_back(std::move(incremented));

      REQUIRE(results.size() == 5);
      REQUIRE(results[0].value == 1);
      REQUIRE(results[1].value == 2);
      REQUIRE(results[2].value == 3);
      REQUIRE(results[3].value == 4);
      REQUIRE(results[4].value == 5);
    }
  }
}
