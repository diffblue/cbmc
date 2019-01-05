/// Author: Diffblue Ltd.

/// \file Tests for depth_iteratort and friends

#include <testing-utils/catch.hpp>
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

/// The mutate_root feature of depth_iteratort can be useful when you have an
/// `exprt` and want to depth iterate its first operand. As part of that
/// iteration you may or may not decide to mutate one of the children,
/// depending on the state of those children. If you do not decide to mutate
/// a child then you probably don't want to call the non-const version of
/// `op0()` because that will break sharing, so you create the depth iterator
/// with the const `exprt` returned from the const invocation of `op0()`, but
/// if you decide during iteration that you do want to mutate a child then
/// you can call the non-const version of `op0()` on the original `exprt` in
/// order to get a non-const `exprt` that the iterator can copy-on-write
/// update to change the child. At this point the iterator needs to be
/// informed that it is now safe to write to the `exprt` it contains. This is
/// achieved by providing a call-back function to the iterator.
SCENARIO("depth_iterator_mutate_root", "[core][utils][depth_iterator]")
{
  GIVEN("A sample expression with a child with id() == ID_1")
  {
    // Set up test expression
    exprt test_expr;
    // This is the expression we will iterate over
    exprt test_root;
    // This is the expression we might mutate when we find it
    exprt test_operand(ID_1);
    test_root.add_to_operands(std::move(test_operand));
    test_expr.add_to_operands(std::move(test_root));
    WHEN("Iteration occurs without mutation")
    {
      // Create shared copies
      exprt original_expr = test_expr;
      exprt expr = original_expr;
      THEN("Shared copy should return object with same address from read()")
      {
        REQUIRE(&expr.read() == &original_expr.read());
      }
      // Create iterator on first operand of expr
      // We don't want to copy-on-write expr, so we get its first operand
      // using a const reference to it
      const exprt &root = static_cast<const exprt &>(expr).op0();
      // This function gets a mutable version of root but in so doing it
      // copy-on-writes expr
      auto get_non_const_root = [&expr]() -> exprt & { return expr.op0(); };
      // Create the iterator over root
      depth_iteratort it = root.depth_begin(get_non_const_root);
      for(; it != root.depth_cend(); ++it)
      {
        if(it->id() == ID_0) // This will never happen
          it.mutate().id(ID_1);
      }
      THEN("No breaking of sharing should have occurred")
      {
        REQUIRE(&expr.read() == &original_expr.read());
      }
    }
    WHEN("Iteration occurs with mutation")
    {
      // Create shared copies
      exprt original_expr = test_expr;
      exprt expr = original_expr;
      THEN("Shared copy should return object with same address from read()")
      {
        REQUIRE(&expr.read() == &original_expr.read());
      }
      // Create iterator on first operand of expr
      // We don't want to copy-on-write expr, so we get its first operand
      // using a const reference to it
      const exprt &root = static_cast<const exprt &>(expr).op0();
      // This function gets a mutable version of root but in so doing it
      // copy-on-writes expr
      auto get_non_const_root = [&expr]() -> exprt & { return expr.op0(); };
      // Create the iterator over root
      depth_iteratort it = root.depth_begin(get_non_const_root);
      for(; it != root.depth_cend(); ++it)
      {
        if(it->id() == ID_1)
          it.mutate().id(ID_0);
      }
      THEN("Breaking of sharing should have occurred")
      {
        REQUIRE(&expr.read() != &original_expr.read());
      }
    }
  }
}
