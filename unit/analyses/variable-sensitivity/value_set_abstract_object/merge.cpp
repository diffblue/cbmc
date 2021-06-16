/*******************************************************************\

 Module: Unit tests for value_set_abstract_valuet::merge

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include "../variable_sensitivity_test_helpers.h"

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>

static merge_result<const value_set_abstract_objectt>
merge(abstract_object_pointert op1, abstract_object_pointert op2)
{
  auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

  return {result.modified, as_value_set(result.object)};
}

SCENARIO(
  "merging value sets",
  "[core][analyses][variable-sensitivity][value_set_abstract_object][merge]")
{
  const typet type = signedbv_typet(32);
  const exprt val1 = from_integer(1, type);
  const exprt val2 = from_integer(2, type);
  const exprt val3 = from_integer(3, type);
  const exprt val4 = from_integer(4, type);
  const exprt val5 = from_integer(5, type);
  const exprt val6 = from_integer(6, type);

  auto object_factory = variable_sensitivity_object_factoryt::configured_with(
    vsd_configt::value_set());
  auto environment = abstract_environmentt{object_factory};
  environment.make_top();
  auto symbol_table = symbol_tablet{};
  auto ns = namespacet{symbol_table};

  GIVEN("merging two value sets")
  {
    WHEN("merging { 1 } with { 1 }")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);

      auto result = merge(op1, op2);

      THEN("result is unmodified { 1 }")
      {
        EXPECT_UNMODIFIED(result, {val1});
      }
    }
    WHEN("merging { 1 } with { 2 }")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_value_set(val2, environment, ns);

      auto result = merge(op1, op2);

      THEN("result is modified { 1, 2 }")
      {
        EXPECT_MODIFIED(result, {val1, val2});
      }
    }
    WHEN("merging { 1, 2 } with { 2 }")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set(val2, environment, ns);

      auto result = merge(op1, op2);

      THEN("result unmodified { 1, 2 }")
      {
        EXPECT_UNMODIFIED(result, {val1, val2});
      }
    }
    WHEN("merging { 1, 2 } with { 3, 4 }")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set({val3, val4}, environment, ns);

      auto result = merge(op1, op2);

      THEN("result is modified { 1, 2, 3, 4 }")
      {
        EXPECT_MODIFIED(result, {val1, val2, val3, val4});
      }
    }
    WHEN("merging { 1, 2, 3 } with { 1, 3, 4 }")
    {
      auto op1 = make_value_set({val1, val2, val3}, environment, ns);
      auto op2 = make_value_set({val1, val3, val4}, environment, ns);

      auto result = merge(op1, op2);

      THEN("result is modified { 1, 2, 3, 4 }")
      {
        EXPECT_MODIFIED(result, {val1, val2, val3, val4});
      }
    }
    WHEN("merging {1, 2} with TOP")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto top2 = make_top_value_set();

      auto merged = merge(op1, top2);

      THEN("result is modified TOP")
      {
        EXPECT_MODIFIED_TOP(merged);
      }
    }
    WHEN("merging {1, 2} with BOTTOM")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto bottom2 = make_bottom_value_set();

      auto merged = merge(op1, bottom2);

      THEN("result is unmodified {1, 2}")
      {
        EXPECT_UNMODIFIED(merged, {val1, val2});
      }
    }
    WHEN("merging TOP with {1, 2}")
    {
      auto top1 = make_top_value_set();
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto merged = merge(top1, op2);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED_TOP(merged);
      }
    }
    WHEN("merging TOP with TOP")
    {
      auto top1 = make_top_value_set();
      auto top2 = make_top_value_set();

      auto merged = merge(top1, top2);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED_TOP(merged);
      }
    }
    WHEN("merging TOP with BOTTOM")
    {
      auto top1 = make_top_value_set();
      auto bottom2 = make_bottom_value_set();

      auto merged = merge(top1, bottom2);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED_TOP(merged);
      }
    }
    WHEN("merging BOTTOM with {1, 2}")
    {
      auto bottom1 = make_bottom_value_set();
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto merged = merge(bottom1, op2);

      THEN("result is modified {1, 2}")
      {
        EXPECT_MODIFIED(merged, {val1, val2});
      }
    }
    WHEN("merging BOTTOM with TOP")
    {
      auto bottom1 = make_bottom_value_set();
      auto top2 = make_top_value_set();

      auto merged = merge(bottom1, top2);

      THEN("result is modified TOP")
      {
        EXPECT_MODIFIED_TOP(merged);
      }
    }
    WHEN("merging BOTTOM with BOTTOM")
    {
      auto bottom1 = make_bottom_value_set();
      auto bottom2 = make_bottom_value_set();

      auto merged = merge(bottom1, bottom2);

      THEN("result is unmodified BOTTOM")
      {
        EXPECT_UNMODIFIED_BOTTOM(merged);
      }
    }
  }

  GIVEN("merging a value_set and an abstract object")
  {
    WHEN("merging {1, 2} with TOP")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto top2 = make_top_object();

      auto merged = merge(op1, top2);

      THEN("result is modified TOP")
      {
        EXPECT_MODIFIED_TOP(merged);
      }
    }
    WHEN("merging {1, 2} with BOTTOM")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto bottom2 = make_bottom_object();

      auto merged = merge(op1, bottom2);

      THEN("result is unmodified {1, 2}")
      {
        EXPECT_UNMODIFIED(merged, {val1, val2});
      }
    }
    WHEN("merging TOP value set with TOP")
    {
      auto top1 = make_top_value_set();
      auto top2 = make_top_object();

      auto merged = merge(top1, top2);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED_TOP(merged);
      }
    }
    WHEN("merging TOP value set with BOTTOM")
    {
      auto top1 = make_top_value_set();
      auto bottom2 = make_bottom_object();

      auto merged = merge(top1, bottom2);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED_TOP(merged);
      }
    }
    WHEN("merging BOTTOM value set with TOP")
    {
      auto bottom1 = make_bottom_value_set();
      auto top2 = make_top_object();

      auto merged = merge(bottom1, top2);

      THEN("result is modified TOP")
      {
        EXPECT_MODIFIED_TOP(merged);
      }
    }
    WHEN("merging BOTTOM value set with BOTTOM")
    {
      auto bottom1 = make_bottom_value_set();
      auto top2 = make_bottom_object();

      auto merged = merge(bottom1, top2);

      THEN("result is unmodified BOTTOM")
      {
        EXPECT_UNMODIFIED_BOTTOM(merged);
      }
    }
  }

  GIVEN("merging a value set and a constant")
  {
    WHEN("merging { 1 } with 1")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto result = merge(op1, op2);

      THEN("result unmodified { 1 }")
      {
        EXPECT_UNMODIFIED(result, {val1});
      }
    }
    WHEN("merging { 1 } with 2")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_constant(val2, environment, ns);

      auto result = merge(op1, op2);

      THEN("result is modified { 1, 2 }")
      {
        EXPECT_MODIFIED(result, {val1, val2});
      }
    }
    WHEN("merging { 1, 2, 3 } with 2")
    {
      auto op1 = make_value_set({val1, val2, val3}, environment, ns);
      auto op2 = make_constant(val2, environment, ns);

      auto result = merge(op1, op2);

      THEN("result is unmodified { 1, 2, 3 }")
      {
        EXPECT_UNMODIFIED(result, {val1, val2, val3});
      }
    }
    WHEN("merging { 1, 3 } with 2")
    {
      auto op1 = make_value_set({val1, val3}, environment, ns);
      auto op2 = make_constant(val2, environment, ns);

      auto result = merge(op1, op2);

      THEN("result is modified { 1, 2, 3 }")
      {
        EXPECT_MODIFIED(result, {val1, val2, val3});
      }
    }
    WHEN("merging BOTTOM with 2")
    {
      auto op1 = make_bottom_value_set();
      auto op2 = make_constant(val2, environment, ns);

      auto result = merge(op1, op2);

      THEN("result is modified { 2 }")
      {
        EXPECT_MODIFIED(result, {val2});
      }
    }
  }

  GIVEN("merging a value_set and an interval")
  {
    auto interval_1_5 = constant_interval_exprt(val1, val5);

    WHEN("merging { 1, 2, 3 } with [1, 5]")
    {
      auto op1 = make_value_set({val1, val3, val5}, environment, ns);
      auto op2 = make_interval(val1, val5, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified { 1, 3, 5, [1, 5]}")
      {
        EXPECT_MODIFIED(merged, {val1, val3, val5, interval_1_5});
      }
    }
    WHEN("merging { [1, 5] } with [1, 5]")
    {
      auto op1 = make_value_set(interval_1_5, environment, ns);
      auto op2 = make_interval(val1, val5, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is unmodified {[1, 5]}")
      {
        EXPECT_UNMODIFIED(merged, {interval_1_5});
      }
    }
    WHEN("merging { 1, 2, [1, 5] } with [1, 5]")
    {
      auto op1 = make_value_set({val1, val2, interval_1_5}, environment, ns);
      auto op2 = make_interval(val1, val5, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is unmodified { 1, 2, [1, 5]}")
      {
        EXPECT_UNMODIFIED(merged, {val1, val2, interval_1_5});
      }
    }
    WHEN("merging BOTTOM with [1, 5]")
    {
      auto op1 = make_bottom_value_set();
      auto op2 = make_interval(val1, val5, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified {[1, 5]}")
      {
        EXPECT_MODIFIED(merged, {interval_1_5});
      }
    }
  }
}
