/*******************************************************************\

Module: Unit tests for dense_integer_map

Author: Diffblue Ltd

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/dense_integer_map.h>

TEST_CASE("no keys", "[core][util][dense_integer_map]")
{
  dense_integer_mapt<int, int> map;
  std::vector<int> empty;
  map.setup_for_keys(empty.begin(), empty.end());

  cbmc_invariants_should_throwt invariants_throw_in_this_scope;

  REQUIRE_THROWS_AS(map.at(0), invariant_failedt);
  REQUIRE_THROWS_AS(map[0], invariant_failedt);
  REQUIRE_THROWS_AS(map.insert({0, 0}), invariant_failedt);
}

TEST_CASE("one key", "[core][util][dense_integer_map]")
{
  dense_integer_mapt<int, int> map;
  std::vector<int> allowed_keys = {1};
  map.setup_for_keys(allowed_keys.begin(), allowed_keys.end());

  cbmc_invariants_should_throwt invariants_throw_in_this_scope;

  REQUIRE(map.size() == 0);

  REQUIRE_THROWS_AS(map.at(1), invariant_failedt);
  REQUIRE(!map.count(1));
  REQUIRE(map[1] == 0);

  REQUIRE(map.size() == 1);
  REQUIRE(map.count(1));

  map[1] = 2;
  REQUIRE(map.at(1) == 2);
  REQUIRE(map[1] == 2);

  auto insert_result = map.insert({1, 5});
  REQUIRE(!insert_result.second);
  REQUIRE(insert_result.first == map.begin());

  REQUIRE_THROWS_AS(map.at(0), invariant_failedt);
  REQUIRE_THROWS_AS(map[0], invariant_failedt);
  REQUIRE_THROWS_AS(map.insert({0, 0}), invariant_failedt);
}

TEST_CASE("insert fresh key", "[core][util][dense_integer_map]")
{
  dense_integer_mapt<int, int> map;
  std::vector<int> allowed_keys = {1};
  map.setup_for_keys(allowed_keys.begin(), allowed_keys.end());

  cbmc_invariants_should_throwt invariants_throw_in_this_scope;

  auto insert_result = map.insert({1, 5});
  REQUIRE(insert_result.second);
  REQUIRE(insert_result.first == map.begin());

  REQUIRE(map.at(1) == 5);
  REQUIRE(map[1] == 5);
}

TEST_CASE("multiple, sparse keys", "[core][util][dense_integer_map]")
{
  dense_integer_mapt<int, int> map;
  std::vector<int> allowed_keys = {1, 10};
  map.setup_for_keys(allowed_keys.begin(), allowed_keys.end());

  cbmc_invariants_should_throwt invariants_throw_in_this_scope;

  REQUIRE(map.size() == 0);

  map.insert({1, 2});
  REQUIRE(map.size() == 1);
  auto second_insert_result = map.insert({10, 11});
  REQUIRE(second_insert_result.second);
  REQUIRE(second_insert_result.first == std::next(map.begin()));

  REQUIRE_THROWS_AS(map[0], invariant_failedt);
  REQUIRE(map[1] == 2);
  // Keys in the gap are silently accepted, though this is bad practice:
  // REQUIRE_THROWS_AS(map[2], invariant_failedt);
  // REQUIRE_THROWS_AS(map[3], invariant_failedt);
  // REQUIRE_THROWS_AS(map[4], invariant_failedt);
  // REQUIRE_THROWS_AS(map[5], invariant_failedt);
  // REQUIRE_THROWS_AS(map[6], invariant_failedt);
  // REQUIRE_THROWS_AS(map[7], invariant_failedt);
  // REQUIRE_THROWS_AS(map[8], invariant_failedt);
  // REQUIRE_THROWS_AS(map[9], invariant_failedt);
  REQUIRE(map[10] == 11);
  REQUIRE_THROWS_AS(map[11], invariant_failedt);
}

TEST_CASE("iterators", "[core][util][dense_integer_map]")
{
  dense_integer_mapt<int, int> map;
  std::vector<int> allowed_keys = {1, 10};
  map.setup_for_keys(allowed_keys.begin(), allowed_keys.end());

  map.insert({1, 5});
  map.insert({10, 11});

  std::vector<std::pair<int, int>> iterator_result{map.begin(), map.end()};
  REQUIRE(
    iterator_result == std::vector<std::pair<int, int>>{{1, 5}, {10, 11}});

  int acc = 0;
  for(auto &key_value : map)
    key_value.second = ++acc;

  iterator_result = std::vector<std::pair<int, int>>{map.begin(), map.end()};
  REQUIRE(iterator_result == std::vector<std::pair<int, int>>{{1, 1}, {10, 2}});

  REQUIRE(map.begin() != map.end());
  REQUIRE(map.begin() != std::next(map.begin()));
  REQUIRE(map.begin() == map.begin());
  REQUIRE(map.size() == 2);
  REQUIRE(std::distance(map.begin(), map.end()) == map.size());

  {
    const auto &const_map = map;

    iterator_result =
      std::vector<std::pair<int, int>>{const_map.begin(), const_map.end()};
    REQUIRE(
      iterator_result == std::vector<std::pair<int, int>>{{1, 1}, {10, 2}});

    auto non_const_iterator = map.begin();
    auto converted_non_const_iterator =
      (decltype(map)::const_iterator)non_const_iterator;
    auto const_iterator = const_map.begin();
    auto other_const_iterator = const_map.begin();

    REQUIRE(converted_non_const_iterator == const_iterator);
    REQUIRE(converted_non_const_iterator == other_const_iterator);
  }
}

TEST_CASE("keys must be unique", "[core][util][dense_integer_map]")
{
  dense_integer_mapt<int, int> map;
  std::vector<int> allowed_keys = {1, 1};

  cbmc_invariants_should_throwt invariants_throw_in_this_scope;

  REQUIRE_THROWS_AS(
    map.setup_for_keys(allowed_keys.begin(), allowed_keys.end()),
    invariant_failedt);

  allowed_keys = {1, 2, 1};
  REQUIRE_THROWS_AS(
    map.setup_for_keys(allowed_keys.begin(), allowed_keys.end()),
    invariant_failedt);

  allowed_keys = {1, 2};
  map.setup_for_keys(allowed_keys.begin(), allowed_keys.end());
}

class reverse_orderingt
{
public:
  int operator()(int x)
  {
    return 10 - x;
  }
};

TEST_CASE(
  "ordering by custom key-to-integer function",
  "[core][util][dense_integer_map]")
{
  dense_integer_mapt<int, int, reverse_orderingt> map;
  std::vector<int> allowed_keys = {-20, 0, 20};

  map.setup_for_keys(allowed_keys.begin(), allowed_keys.end());
  map.insert({0, 1});
  map.insert({-20, 2});
  map.insert({20, 3});

  std::vector<std::pair<int, int>> iterator_result{map.begin(), map.end()};

  REQUIRE(
    iterator_result ==
    std::vector<std::pair<int, int>>{{20, 3}, {0, 1}, {-20, 2}});
}

class index_is_mod2t
{
public:
  int operator()(int x)
  {
    return x % 2;
  }
};

TEST_CASE("indices must be unique", "[core][util][dense_integer_map]")
{
  dense_integer_mapt<int, int, index_is_mod2t> map;

  cbmc_invariants_should_throwt invariants_throw_in_this_scope;

  // Illegal keys (are equal mod 2)
  std::vector<int> allowed_keys = {2, 4};
  REQUIRE_THROWS_AS(
    map.setup_for_keys(allowed_keys.begin(), allowed_keys.end()),
    invariant_failedt);

  // Legal keys (not equal mod 2)
  allowed_keys = {2, 3};
  map.setup_for_keys(allowed_keys.begin(), allowed_keys.end());
}
