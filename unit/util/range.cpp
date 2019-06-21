/*******************************************************************\

Module: Unit tests for range

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <list>
#include <vector>

#include <testing-utils/use_catch.h>
#include <util/range.h>

/// Trivial example template function requiring a container to have a
/// `value_type`.
template <typename containert>
typename containert::value_type front(containert container)
{
  return *container.begin();
}

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
      const auto range = make_range(list);
      std::size_t total_length = 0;
      for(const auto &s : range)
        total_length += s.length();
      REQUIRE(total_length == 12);
    }
    THEN("Use map to compute individual lengths")
    {
      const auto length_range =
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
      const auto filtered_range = make_range(list).filter(
        [&](const std::string &s) { return s.length() == 4; });
      auto it = filtered_range.begin();
      REQUIRE(*it == "cdef");
      ++it;
      REQUIRE(it == filtered_range.end());
    }

    THEN("Drop first 2 elements")
    {
      auto range = make_range(list);
      auto drop_range = range.drop(2);
      auto it = drop_range.begin();
      REQUIRE(*it == "acdef");
      drop_range = std::move(drop_range).drop(1);
      REQUIRE(drop_range.empty());
      // Check the original is unmodified
      REQUIRE(!range.empty());
      REQUIRE(*range.begin() == "abc");
    }
    THEN("Drop first 5 elements")
    {
      auto range = make_range(list);
      auto skip_range = range.drop(5);
      REQUIRE(skip_range.empty());
      // Check the original is unmodified
      REQUIRE(!range.empty());
      REQUIRE(*range.begin() == "abc");
    }
    THEN("Drop first 2 elements, move version")
    {
      auto range = make_range(list);
      range = std::move(range).drop(2);
      REQUIRE(!range.empty());
      auto it = range.begin();
      REQUIRE(*it == "acdef");
      range = std::move(range).drop(1);
      REQUIRE(range.empty());
    }
    THEN("Drop first 5 elements, move version")
    {
      auto range = make_range(list);
      range = std::move(range).drop(5);
      REQUIRE(range.empty());
    }

    THEN(
      "A const instance of a `filter_iteratort` can mutate the input "
      "collection.")
    {
      const auto it =
        make_range(list)
          .filter([&](const std::string &s) { return s.length() == 3; })
          .begin();
      *it += "x";
      REQUIRE(*list.begin() == "abcx");
    }
    THEN("Filter, map and use range-for on the same list")
    {
      const auto range =
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
  GIVEN("A const vector of ints")
  {
    const std::vector<int> input{1, 2, 3, 4};
    THEN("Filter the vector using range.")
    {
      const auto odds_range =
        make_range(input).filter([](const int number) { return number % 2; });
      const std::vector<int> odds{odds_range.begin(), odds_range.end()};
      const std::vector<int> expected_odds{1, 3};
      REQUIRE(odds == expected_odds);
    }
    THEN(
      "The unit testing template function requiring `value_type` works with "
      "`std::vector`.")
    {
      REQUIRE(front(input) == 1);
    }
    THEN(
      "A range can be used with a template function expecting a container "
      "which has a `value_type`.")
    {
      REQUIRE(front(make_range(input)) == 1);
    }
    THEN("Map over the vector using range.")
    {
      const auto plus_one_range =
        make_range(input).map([](const int number) { return number + 1; });
      const std::vector<int> plus_one_collection{plus_one_range.begin(),
                                                 plus_one_range.end()};
      const std::vector<int> expected_output{2, 3, 4, 5};
      REQUIRE(plus_one_collection == expected_output);
    };
  }
  GIVEN("Two const vectors of ints")
  {
    const std::vector<int> input1{1, 2};
    const std::vector<int> input2{3, 4};
    THEN("Concat the vectors using range.")
    {
      const auto range = make_range(input1).concat(make_range(input2));
      const std::vector<int> output{range.begin(), range.end()};
      const std::vector<int> expected{1, 2, 3, 4};
      REQUIRE(output == expected);
    };
  }
  GIVEN("Two non-const vectors of ints.")
  {
    std::vector<int> input1{1, 2};
    std::vector<int> input2{3, 4};
    THEN(
      "Const instances of `concat_iteratort` should enable the input "
      "collections to be mutated.")
    {
      const auto concat_range = make_range(input1).concat(make_range(input2));
      int x = 5;
      for(auto it = concat_range.begin(); it != concat_range.end(); ++it, ++x)
      {
        const auto const_it = it;
        *const_it = x;
      }
      std::vector<int> expected_result1{5, 6};
      std::vector<int> expected_result2{7, 8};
      REQUIRE(input1 == expected_result1);
      REQUIRE(input2 == expected_result2);
    }
  }
  GIVEN("A vectors of int and a list of strings of same sizes.")
  {
    std::vector<int> int_vector{1, 2};
    std::list<std::string> string_list{"foo", "bar"};
    WHEN("We zip the vector and the list")
    {
      auto range = make_range(int_vector).zip(string_list);
      REQUIRE(!range.empty());
      THEN("First pair is (1, foo)")
      {
        const std::pair<int, std::string> first_pair = *range.begin();
        REQUIRE(first_pair.first == 1);
        REQUIRE(first_pair.second == "foo");
      }
      range = std::move(range).drop(1);
      THEN("Second pair is (2, bar)")
      {
        const std::pair<int, std::string> second_pair = *range.begin();
        REQUIRE(second_pair.first == 2);
        REQUIRE(second_pair.second == "bar");
      }
      range = std::move(range).drop(1);
      THEN("Range is empty")
      {
        REQUIRE(range.empty());
      }
    }
  }
  GIVEN("A constant vectors of int and a list of strings of same sizes.")
  {
    const std::vector<int> int_vector{41, 27};
    const std::list<std::string> string_list{"boo", "far"};
    WHEN("We zip the vector and the list")
    {
      auto range = make_range(int_vector).zip(string_list);
      REQUIRE(!range.empty());
      THEN("First pair is (1, foo)")
      {
        const std::pair<int, std::string> first_pair = *range.begin();
        REQUIRE(first_pair.first == 41);
        REQUIRE(first_pair.second == "boo");
      }
      range = std::move(range).drop(1);
      THEN("Second pair is (2, bar)")
      {
        const std::pair<int, std::string> second_pair = *range.begin();
        REQUIRE(second_pair.first == 27);
        REQUIRE(second_pair.second == "far");
      }
      range = std::move(range).drop(1);
      THEN("Range is empty")
      {
        REQUIRE(range.empty());
      }
    }
  }
  GIVEN("Two vectors, where the first is shorter.")
  {
    const std::vector<int> int_vector{814, 51};
    const std::vector<std::string> string_vector{"foo", "bar", "baz", "bay"};
    WHEN("We zip the vectors with same_size=false")
    {
      auto range = make_range(int_vector).zip<false>(string_vector);
      REQUIRE(!range.empty());
      THEN("First pair is (814, foo)")
      {
        const std::pair<int, std::string> first_pair = *range.begin();
        REQUIRE(first_pair.first == 814);
        REQUIRE(first_pair.second == "foo");
      }
      auto second_range = range.drop(1);
      THEN("Begin iterator when first element is dropped is different")
      {
        REQUIRE(second_range.begin() != range.begin());
      }
      THEN("Second pair is (51, bar)")
      {
        const std::pair<int, std::string> second_pair = *second_range.begin();
        REQUIRE(second_pair.first == 51);
        REQUIRE(second_pair.second == "bar");
      }
      auto third_range = second_range.drop(1);
      THEN("Range is empty")
      {
        REQUIRE(third_range.begin() != second_range.begin());
        REQUIRE(third_range.empty());
      }
    }
    WHEN("We zip the vectors with same_size=true")
    {
      auto range = make_range(int_vector).zip<true>(string_vector);
      REQUIRE(!range.empty());
      THEN("First pair is (814, foo)")
      {
        const std::pair<int, std::string> first_pair = *range.begin();
        REQUIRE(first_pair.first == 814);
        REQUIRE(first_pair.second == "foo");
      }
      auto second_range = range.drop(1);
      THEN("Begin iterator when first element is dropped is different")
      {
        REQUIRE(second_range.begin() != range.begin());
      }
      THEN("Second pair is (51, bar)")
      {
        const std::pair<int, std::string> second_pair = *second_range.begin();
        REQUIRE(second_pair.first == 51);
        REQUIRE(second_pair.second == "bar");
      }
      THEN("An invariant throw as we reach the end of the first range")
      {
        cbmc_invariants_should_throwt invariants_throw;
        REQUIRE_THROWS_AS(second_range.drop(1), invariant_failedt);
      }
    }
  }
  GIVEN("Two vectors, where the second is shorter.")
  {
    const std::vector<std::string> string_vector{"foo", "bar", "baz", "bay"};
    const std::vector<int> int_vector{814, 51};
    WHEN("We zip the vectors with same_size=false")
    {
      auto range = make_range(string_vector).zip<false>(int_vector);
      REQUIRE(!range.empty());
      THEN("First pair is (foo, 814)")
      {
        const std::pair<std::string, int> first_pair = *range.begin();
        REQUIRE(first_pair.first == "foo");
        REQUIRE(first_pair.second == 814);
      }
      auto second_range = range.drop(1);
      THEN("Begin iterator when first element is dropped is different")
      {
        REQUIRE(second_range.begin() != range.begin());
      }
      THEN("Second pair is (51, bar)")
      {
        const std::pair<std::string, int> second_pair = *second_range.begin();
        REQUIRE(second_pair.first == "bar");
        REQUIRE(second_pair.second == 51);
      }
      auto third_range = second_range.drop(1);
      THEN("Range is empty")
      {
        REQUIRE(third_range.begin() != second_range.begin());
        REQUIRE(third_range.empty());
      }
    }
    WHEN("We zip the vectors with same_size=true")
    {
      auto range = make_range(string_vector).zip<true>(int_vector);
      REQUIRE(!range.empty());
      THEN("First pair is (foo, 814)")
      {
        const std::pair<std::string, int> first_pair = *range.begin();
        REQUIRE(first_pair.first == "foo");
        REQUIRE(first_pair.second == 814);
      }
      auto second_range = range.drop(1);
      THEN("Begin iterator when first element is dropped is different")
      {
        REQUIRE(second_range.begin() != range.begin());
      }
      THEN("Second pair is (bar, 51)")
      {
        const std::pair<std::string, int> second_pair = *second_range.begin();
        REQUIRE(second_pair.first == "bar");
        REQUIRE(second_pair.second == 51);
      }
      THEN("An invariant throw as we reach the end of the first range")
      {
        cbmc_invariants_should_throwt invariants_throw;
        REQUIRE_THROWS_AS(second_range.drop(1), invariant_failedt);
      }
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
      const auto input_range = make_range(input);
      move_onlyt destination{std::move(*input_range.begin())};
      REQUIRE(destination.value == 1);
    }
    THEN("A range of made from the vector can be filtered.")
    {
      const auto odds_filter = make_range(input).filter(is_odd);
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
