/*******************************************************************\

 Module: Example Catch Tests

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <catch.hpp>
#include <util/expr.h>
#include <util/expr_iterator.h>

TEST_CASE("Depth iterator over empty exprt")
{
  exprt expr;
  std::vector<std::reference_wrapper<const exprt>> results;
  std::copy(expr.depth_begin(),
            expr.depth_end(),
            std::back_inserter(results));
  REQUIRE(results.size()==1);
  REQUIRE(results.front().get()==expr);
}

TEST_CASE("Unique depth iterator over empty exprt")
{
  exprt expr;
  std::vector<std::reference_wrapper<const exprt>> results;
  std::copy(expr.unique_depth_begin(),
            expr.unique_depth_end(),
            std::back_inserter(results));
  REQUIRE(results.size()==1);
  REQUIRE(results.front().get()==expr);
}

TEST_CASE("Iterate over a node with 3 children")
{
  std::vector<exprt> input(4);
  input[0].operands()={ input[1], input[2], input[3] };
  std::vector<std::reference_wrapper<const exprt>> results;
  std::copy(input[0].depth_begin(),
            input[0].depth_end(),
            std::back_inserter(results));
  REQUIRE(results.size()==input.size());

  auto it=results.begin();
  for(const auto &expr : input)
  {
    REQUIRE(it->get()==expr);
    it++;
  }
}

TEST_CASE("Iterate over a node with 5 children, ignoring duplicates")
{
  std::vector<exprt> input(4);
  input[1].id(ID_int);
  input[2].id(ID_symbol);
  input[3].id(ID_array);
  input[0].operands()={ input[1], input[2], input[1], input[3], input[2] };
  std::vector<std::reference_wrapper<const exprt>> results;
  std::copy(input[0].unique_depth_begin(),
            input[0].unique_depth_end(),
            std::back_inserter(results));
  REQUIRE(results.size()==input.size());

  auto it=results.begin();
  for(const auto &expr : input)
  {
    REQUIRE(it->get()==expr);
    it++;
  }
}

TEST_CASE("Iterate over a 3-level node")
{
  std::vector<exprt> input(4);
  input[1].id(ID_int);
  input[2].operands()={ input[3] };
  input[0].operands()={ input[1], input[2] };
  std::vector<std::reference_wrapper<const exprt>> results;
  std::copy(input[0].depth_begin(),
            input[0].depth_end(),
            std::back_inserter(results));
  REQUIRE(results.size()==input.size());

  auto it=results.begin();
  for(const auto &expr : input)
  {
    REQUIRE(it->get()==expr);
    it++;
  }
}

TEST_CASE("Iterate over a 3-level tree, ignoring duplicates")
{
  std::vector<exprt> input(4);
  input[1].id(ID_int);
  input[2].operands()={ input[3], input[1] };
  input[0].operands()={ input[1], input[2], input[3] };
  std::vector<std::reference_wrapper<const exprt>> results;
  std::copy(input[0].unique_depth_begin(),
            input[0].unique_depth_end(),
            std::back_inserter(results));
  REQUIRE(results.size()==input.size());

  auto it=results.begin();
  for(const auto &expr : input)
  {
    REQUIRE(it->get()==expr);
    it++;
  }
}

TEST_CASE("Iterate over a 3-level tree, mutate - set all types to ID_symbol")
{
  std::vector<exprt> input(4);
  input[1].id(ID_int);
  input[2].operands()={ input[3] };
  input[0].operands()={ input[1], input[2] };
  std::vector<std::reference_wrapper<exprt>> results;
  for(auto it=input[0].depth_begin(),
           end=input[0].depth_end();
      it != end; ++it)
  {
    exprt &expr=it.mutate();
    results.push_back(std::ref(expr));
    REQUIRE(*it==expr);
    expr.id(ID_symbol);
  }
  REQUIRE(results.size()==input.size());
  for(const auto& expr : results)
  {
    REQUIRE(expr.get().id()==ID_symbol);
  }
}

TEST_CASE("next_sibling_or_parent, next sibling")
{
  std::vector<exprt> input(4);
  input[1].operands()={ input[3] };
  input[2].id(ID_int);
  input[0].operands()={ input[1], input[2] };
  auto it=input[0].depth_begin();
  it++;
  it.next_sibling_or_parent();
  REQUIRE(*it==input[2]);
}

TEST_CASE("next_sibling_or_parent, next parent ")
{
  std::vector<exprt> input(3);
  input[1].operands()={ input[2] };
  input[0].operands()={ input[1] };
  auto it=input[0].depth_begin();
  it++;
  it.next_sibling_or_parent();
  REQUIRE(it==input[0].depth_end());
}
