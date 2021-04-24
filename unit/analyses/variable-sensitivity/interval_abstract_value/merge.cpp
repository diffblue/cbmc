/*******************************************************************\

 Module: Unit tests for interval_abstract_valuet::merge

 Author: Jez Higgins.

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>

static merge_result<const interval_abstract_valuet>
merge(abstract_object_pointert op1, abstract_object_pointert op2)
{
  auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

  return {result.modified, as_interval(result.object)};
}

SCENARIO(
  "merge interval_abstract_value",
  "[core][analyses][variable-sensitivity][interval_abstract_value][merge]")
{
  const typet type = signedbv_typet(32);
  const exprt val1 = from_integer(1, type);
  const exprt val2 = from_integer(2, type);
  const exprt val3 = from_integer(3, type);
  const exprt val4 = from_integer(4, type);
  const exprt val5 = from_integer(5, type);
  const exprt val6 = from_integer(6, type);

  auto config = vsd_configt::constant_domain();
  config.context_tracking.data_dependency_context = false;
  config.context_tracking.last_write_context = false;
  auto object_factory =
    variable_sensitivity_object_factoryt::configured_with(config);
  abstract_environmentt environment{object_factory};
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("merging two intervals")
  {
    WHEN("merging [1, 2] with [1, 2]")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_interval(val1, val2, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is unmodified [1, 2]")
      {
        EXPECT_UNMODIFIED(merged, val1, val2);
      }
    }
    WHEN("merging [1, 5] with [2, 3]")
    {
      auto op1 = make_interval(val1, val5, environment, ns);
      auto op2 = make_interval(val2, val3, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is unmodified [1, 5]")
      {
        EXPECT_UNMODIFIED(merged, val1, val5);
      }
    }
    WHEN("merging [2, 3] with [1, 5]")
    {
      auto op1 = make_interval(val2, val3, environment, ns);
      auto op2 = make_interval(val1, val5, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified [1, 5]")
      {
        EXPECT_MODIFIED(merged, val1, val5);
      }
    }
    WHEN("merging [1, 2] with [4, 5]")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_interval(val4, val5, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified [1, 5]")
      {
        EXPECT_MODIFIED(merged, val1, val5);
      }
    }
    WHEN("merging [4, 5] with [1, 2]")
    {
      auto op1 = make_interval(val4, val5, environment, ns);
      auto op2 = make_interval(val1, val2, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified [1, 5]")
      {
        EXPECT_MODIFIED(merged, val1, val5);
      }
    }
    WHEN("merging [2, 4] with [1, 3]")
    {
      auto op1 = make_interval(val2, val4, environment, ns);
      auto op2 = make_interval(val1, val3, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified [1, 4]")
      {
        EXPECT_MODIFIED(merged, val1, val4);
      }
    }
    WHEN("merging [1, 3] with [2, 4]")
    {
      auto op1 = make_interval(val1, val3, environment, ns);
      auto op2 = make_interval(val2, val4, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified [1, 4]")
      {
        EXPECT_MODIFIED(merged, val1, val4);
      }
    }
    WHEN("merging [1, 2] with TOP")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto top2 = make_top_interval();

      auto merged = merge(op1, top2);

      THEN("result is modified TOP")
      {
        EXPECT_MODIFIED_TOP(merged);
      }
    }
    WHEN("merging [1, 2] with BOTTOM")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto bottom2 = make_bottom_interval();

      auto merged = merge(op1, bottom2);

      THEN("result is unmodified [1, 2]")
      {
        EXPECT_UNMODIFIED(merged, val1, val2);
      }
    }
    WHEN("merging TOP with [1, 2]")
    {
      auto top1 = make_top_interval();
      auto op2 = make_interval(val1, val2, environment, ns);

      auto merged = merge(top1, op2);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED_TOP(merged);
      }
    }
    WHEN("merging TOP with TOP")
    {
      auto top1 = make_top_interval();
      auto top2 = make_top_interval();

      auto merged = merge(top1, top2);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED_TOP(merged);
      }
    }
    WHEN("merging TOP with BOTTOM")
    {
      auto top1 = make_top_interval();
      auto bottom2 = make_bottom_interval();

      auto merged = merge(top1, bottom2);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED_TOP(merged);
      }
    }
    WHEN("merging BOTTOM with [1, 2]")
    {
      auto bottom1 = make_bottom_interval();
      auto op2 = make_interval(val1, val2, environment, ns);

      auto merged = merge(bottom1, op2);

      THEN("result is modified [1, 2]")
      {
        EXPECT_MODIFIED(merged, val1, val2);
      }
    }
    WHEN("merging BOTTOM with TOP")
    {
      auto bottom1 = make_bottom_interval();
      auto top2 = make_top_interval();

      auto merged = merge(bottom1, top2);

      THEN("result is modified TOP")
      {
        EXPECT_MODIFIED_TOP(merged);
      }
    }
    WHEN("merging BOTTOM with BOTTOM")
    {
      auto bottom1 = make_bottom_interval();
      auto bottom2 = make_bottom_interval();

      auto merged = merge(bottom1, bottom2);

      THEN("result is unmodified BOTTOM")
      {
        EXPECT_UNMODIFIED_BOTTOM(merged);
      }
    }
  }

  GIVEN("merging an interval and an abstract object")
  {
    WHEN("merging[1, 2] with TOP")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto top2 = make_top_object();

      auto merged = merge(op1, top2);

      THEN("result is modified TOP")
      {
        EXPECT_MODIFIED_TOP(merged);
      }
    }
    WHEN("merging[1, 2] with BOTTOM")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto bottom2 = make_bottom_object();

      auto merged = merge(op1, bottom2);

      THEN("result is unmodified [1, 2]")
      {
        EXPECT_UNMODIFIED(merged, val1, val2);
      }
    }
    WHEN("merging TOP interval with TOP")
    {
      auto top1 = make_top_interval();
      auto top2 = make_top_object();

      auto merged = merge(top1, top2);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED_TOP(merged);
      }
    }
    WHEN("merging TOP interval with BOTTOM")
    {
      auto top1 = make_top_interval();
      auto bottom2 = make_bottom_object();

      auto merged = merge(top1, bottom2);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED_TOP(merged);
      }
    }
    WHEN("merging BOTTOM interval with TOP")
    {
      auto bottom1 = make_bottom_interval();
      auto top2 = make_top_object();

      auto merged = merge(bottom1, top2);

      THEN("result is modified TOP")
      {
        EXPECT_MODIFIED_TOP(merged);
      }
    }
    WHEN("merging BOTTOM interval with BOTTOM")
    {
      auto bottom1 = make_bottom_interval();
      auto top2 = make_bottom_object();

      auto merged = merge(bottom1, top2);

      THEN("result is unmodified BOTTOM")
      {
        EXPECT_UNMODIFIED_BOTTOM(merged);
      }
    }
  }

  GIVEN("merging an interval and a constant")
  {
    WHEN("merging [1, 5] with 1")
    {
      auto op1 = make_interval(val1, val5, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is unmodified [1, 5]")
      {
        EXPECT_UNMODIFIED(merged, val1, val5);
      }
    }
    WHEN("merging [1, 5] with 3")
    {
      auto op1 = make_interval(val1, val5, environment, ns);
      auto op2 = make_constant(val3, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is unmodified [1, 5]")
      {
        EXPECT_UNMODIFIED(merged, val1, val5);
      }
    }
    WHEN("merging [1, 5] with 5")
    {
      auto op1 = make_interval(val1, val5, environment, ns);
      auto op2 = make_constant(val5, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is unmodified [1, 5]")
      {
        EXPECT_UNMODIFIED(merged, val1, val5);
      }
    }
    WHEN("merging [3, 4] with 6")
    {
      auto op1 = make_interval(val3, val4, environment, ns);
      auto op2 = make_constant(val6, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified [3, 6]")
      {
        EXPECT_MODIFIED(merged, val3, val6);
      }
    }
    WHEN("merging [3, 4] with 1")
    {
      auto op1 = make_interval(val3, val4, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified [1, 4]")
      {
        EXPECT_MODIFIED(merged, val1, val4);
      }
    }
    WHEN("merging BOTTOM with 3")
    {
      auto op1 = make_bottom_interval();
      auto op2 = make_constant(val3, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified [3, 3]")
      {
        EXPECT_MODIFIED(merged, val3, val3);
      }
    }
  }

  GIVEN("merging an interval and a value_set")
  {
    WHEN("merging [1, 5] with { 1, 3, 5 }")
    {
      auto op1 = make_interval(val1, val5, environment, ns);
      auto op2 = make_value_set({val1, val3, val5}, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is unmodified [1, 5]")
      {
        EXPECT_UNMODIFIED(merged, val1, val5);
      }
    }
    WHEN("merging [1, 5] with { 3 }")
    {
      auto op1 = make_interval(val1, val5, environment, ns);
      auto op2 = make_value_set({val3}, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is unmodified [1, 5]")
      {
        EXPECT_UNMODIFIED(merged, val1, val5);
      }
    }
    WHEN("merging [3, 4] with { 6 }")
    {
      auto op1 = make_interval(val3, val4, environment, ns);
      auto op2 = make_value_set({val6}, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified [3, 6]")
      {
        EXPECT_MODIFIED(merged, val3, val6);
      }
    }
    WHEN("merging [3, 4] with { 4, 6 }")
    {
      auto op1 = make_interval(val3, val4, environment, ns);
      auto op2 = make_value_set({val4, val6}, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified [3, 6]")
      {
        EXPECT_MODIFIED(merged, val3, val6);
      }
    }
    WHEN("merging [3, 4] with { 1 }")
    {
      auto op1 = make_interval(val3, val4, environment, ns);
      auto op2 = make_value_set({val1}, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified [1, 4]")
      {
        EXPECT_MODIFIED(merged, val1, val4);
      }
    }
    WHEN("merging [3, 4] with { 1, 3 }")
    {
      auto op1 = make_interval(val3, val4, environment, ns);
      auto op2 = make_value_set({val1, val3}, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified [1, 4]")
      {
        EXPECT_MODIFIED(merged, val1, val4);
      }
    }
    WHEN("merging [3, 4] with { [4, 6] }")
    {
      auto op1 = make_interval(val3, val4, environment, ns);
      auto op2 =
        make_value_set({constant_interval_exprt(val4, val6)}, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified [3, 6]")
      {
        EXPECT_MODIFIED(merged, val3, val6);
      }
    }
    WHEN("merging [3, 4] with { 1, [3, 3] }")
    {
      auto op1 = make_interval(val3, val4, environment, ns);
      auto op2 = make_value_set(
        {val1, constant_interval_exprt(val3, val3)}, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified [1, 4]")
      {
        EXPECT_MODIFIED(merged, val1, val4);
      }
    }
    WHEN("merging BOTTOM with { 3 }")
    {
      auto op1 = make_bottom_interval();
      auto op2 = make_value_set({val3}, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified [3, 3]")
      {
        EXPECT_MODIFIED(merged, val3, val3);
      }
    }
    WHEN("merging BOTTOM with { 1, 3, 6 }")
    {
      auto op1 = make_bottom_interval();
      auto op2 = make_value_set({val1, val3, val6}, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result is modified [1, 6]")
      {
        EXPECT_MODIFIED(merged, val1, val6);
      }
    }
  }
}
