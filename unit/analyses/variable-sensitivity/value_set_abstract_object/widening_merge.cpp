/*******************************************************************\

 Module: Unit tests for value_set_abstract_objectt::merge

 Author: Jez Higgins.

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>

static merge_result<const value_set_abstract_objectt>
widening_merge(abstract_object_pointert op1, abstract_object_pointert op2)
{
  auto result = abstract_objectt::merge(op1, op2, widen_modet::could_widen);

  return {result.modified, as_value_set(result.object)};
}

SCENARIO(
  "widening merge value_set_abstract_object",
  "[core][analyses][variable-sensitivity][value_set_abstract_object][merge]")
{
  auto type = signedbv_typet(32);
  auto val0 = from_integer(0, type);
  auto val1 = from_integer(1, type);
  auto val2 = from_integer(2, type);
  auto val3 = from_integer(3, type);
  auto val4 = from_integer(4, type);
  auto val5 = from_integer(5, type);
  auto val6 = from_integer(6, type);
  auto val7 = from_integer(7, type);
  auto val8 = from_integer(8, type);
  auto val9 = from_integer(9, type);
  auto val10 = from_integer(10, type);
  auto val11 = from_integer(11, type);
  auto val12 = from_integer(12, type);
  auto val13 = from_integer(13, type);
  auto val1minus = from_integer(-1, type);
  auto val2minus = from_integer(-2, type);
  auto val3minus = from_integer(-3, type);
  auto val4minus = from_integer(-4, type);
  auto val5minus = from_integer(-5, type);
  auto val8minus = from_integer(-8, type);
  auto val10minus = from_integer(-10, type);
  auto valMax = max_exprt(type);
  auto valMin = min_exprt(type);
  auto veryLarge = from_integer(2 << 29, type);
  auto veryLargeMinus = from_integer(-(2 << 29), type);

  auto config = vsd_configt::constant_domain();
  config.context_tracking.data_dependency_context = false;
  config.context_tracking.last_write_context = false;
  auto object_factory =
    variable_sensitivity_object_factoryt::configured_with(config);
  abstract_environmentt environment{object_factory};
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("value_set merges which don't widen")
  {
    WHEN("merging {1, 2} with {1, 2}")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is unmodified {1, 2}")
      {
        EXPECT_UNMODIFIED(merged, {val1, val2});
      }
    }
    WHEN("merging {1, 5} with {2, 3}")
    {
      auto op1 = make_value_set({val1, val5}, environment, ns);
      auto op2 = make_value_set({val2, val3}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is unmodified {1, 2, 3, 5}")
      {
        EXPECT_MODIFIED(merged, {val1, val2, val3, val5});
      }
    }
    WHEN("merging { 1, 4, 7, 10, 13 } with { 2, 3, 5, 6, 8, 9, 11, 12 }")
    {
      auto op1 =
        make_value_set({val1, val4, val7, val10, val13}, environment, ns);
      auto op2 = make_value_set(
        {val2, val3, val5, val6, val8, val9, val11, val12}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is compacted but not widened { [1, 5], 6, 7, 8, [9, 13]")
      {
        auto interval_1_5 = constant_interval_exprt(val1, val5);
        auto interval_9_13 = constant_interval_exprt(val9, val13);
        EXPECT_MODIFIED(
          merged, {interval_1_5, val6, val7, val8, interval_9_13});
      }
    }
  }

  GIVEN("widening merges with TOP or BOTTOM")
  {
    WHEN("merging {1, 2} with TOP")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto top2 = make_top_value_set();

      auto merged = widening_merge(op1, top2);

      THEN("result is modified TOP")
      {
        EXPECT_MODIFIED_TOP(merged);
      }
    }
    WHEN("merging {1, 2} with BOTTOM")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto bottom2 = make_bottom_value_set();

      auto merged = widening_merge(op1, bottom2);

      THEN("result is unmodified {1, 2}")
      {
        EXPECT_UNMODIFIED(merged, {val1, val2});
      }
    }
    WHEN("merging TOP with {1, 2}")
    {
      auto top1 = make_top_value_set();
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto merged = widening_merge(top1, op2);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED_TOP(merged);
      }
    }
    WHEN("merging BOTTOM with {1, 2}")
    {
      auto bottom1 = make_bottom_value_set();
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto merged = widening_merge(bottom1, op2);

      THEN("result is modified {1, 2}")
      {
        EXPECT_MODIFIED(merged, {val1, val2});
      }
    }
    WHEN("merging TOP with TOP")
    {
      auto top1 = make_top_value_set();
      auto top2 = make_top_value_set();

      auto merged = widening_merge(top1, top2);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED_TOP(merged);
      }
    }
    WHEN("merging TOP with BOTTOM")
    {
      auto top1 = make_top_value_set();
      auto bottom2 = make_bottom_value_set();

      auto merged = widening_merge(top1, bottom2);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED_TOP(merged);
      }
    }
    WHEN("merging BOTTOM with TOP")
    {
      auto bottom1 = make_bottom_value_set();
      auto top2 = make_top_value_set();

      auto merged = widening_merge(bottom1, top2);

      THEN("result is modified TOP")
      {
        EXPECT_MODIFIED_TOP(merged);
      }
    }
    WHEN("merging BOTTOM with BOTTOM")
    {
      auto bottom1 = make_bottom_value_set();
      auto bottom2 = make_bottom_value_set();

      auto merged = widening_merge(bottom1, bottom2);

      THEN("result is unmodified BOTTOM")
      {
        EXPECT_UNMODIFIED_BOTTOM(merged);
      }
    }
  }

  GIVEN("value_set merges which do widen")
  {
    WHEN("merging {1, 3} with {2, 4}")
    {
      auto op1 = make_value_set({val1, val3}, environment, ns);
      auto op2 = make_value_set({val2, val4}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen upper bound - {1, 2, 3, [4, 8]}")
      {
        auto interval_4_8 = constant_interval_exprt(val4, val8);
        EXPECT_MODIFIED(merged, {val1, val2, val3, interval_4_8});
      }
    }
    WHEN("merging {2, 4} with {1, 3}")
    {
      auto op1 = make_value_set({val2, val4}, environment, ns);
      auto op2 = make_value_set({val1, val3}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen lower bound - {[-3, 1], 2, 3, 4}")
      {
        auto interval_3minus_1 =
          constant_interval_exprt(from_integer(-3, type), val1);
        EXPECT_MODIFIED(merged, {val2, val3, val4, interval_3minus_1});
      }
    }
    WHEN("merging {1, 2} with {4, 5}")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set({val4, val5}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen upper bound - {1, 2, 4, [5, 10]")
      {
        auto interval_5_10 = constant_interval_exprt(val5, val10);
        EXPECT_MODIFIED(merged, {val1, val2, val4, interval_5_10});
      }
    }
    WHEN("merging {4, 5} with {1, 2}")
    {
      auto op1 = make_value_set({val4, val5}, environment, ns);
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen lower bound - {[-4, 1], 2, 4, 5}")
      {
        auto interval_4minus_1 =
          constant_interval_exprt(from_integer(-4, type), val1);
        EXPECT_MODIFIED(merged, {interval_4minus_1, val2, val4, val4});
      }
    }
    WHEN("merging {[1, 3]} with {2, 4}")
    {
      auto interval_1_3 = constant_interval_exprt(val1, val3);
      auto op1 = make_value_set(interval_1_3, environment, ns);
      auto op2 = make_value_set({val2, val4}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen upper-bound, {[1, 3], 2 [4, 8]}")
      {
        auto interval_4_8 = constant_interval_exprt(val4, val8);
        EXPECT_MODIFIED(merged, {interval_1_3, val2, interval_4_8});
      }
    }
    WHEN("merging {[1, 3]} with {[2, 4]}")
    {
      auto interval_1_3 = constant_interval_exprt(val1, val3);
      auto interval_2_4 = constant_interval_exprt(val2, val4);
      auto op1 = make_value_set(interval_1_3, environment, ns);
      auto op2 = make_value_set(interval_2_4, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen upper-bound, {[1, 3], [2, 8]}")
      {
        auto interval_2_8 = constant_interval_exprt(val2, val8);
        EXPECT_MODIFIED(merged, {interval_1_3, interval_2_8});
      }
    }
    WHEN("merging {[2, 4]} with {1, 3}")
    {
      auto interval_2_4 = constant_interval_exprt(val2, val4);
      auto op1 = make_value_set(interval_2_4, environment, ns);
      auto op2 = make_value_set({val1, val3}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen lower bound - {[-3, 1], 3, [2, 4]}")
      {
        auto interval_3minus_1 =
          constant_interval_exprt(from_integer(-3, type), val1);
        EXPECT_MODIFIED(merged, {interval_2_4, val3, interval_3minus_1});
      }
    }
    WHEN("merging {[2, 4]} with {[1, 3]}")
    {
      auto interval_2_4 = constant_interval_exprt(val2, val4);
      auto interval_1_3 = constant_interval_exprt(val1, val3);
      auto op1 = make_value_set(interval_2_4, environment, ns);
      auto op2 = make_value_set(interval_1_3, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen lower bound - {[-3, 3], [2, 4]}")
      {
        auto interval_3minus_3 =
          constant_interval_exprt(from_integer(-3, type), val3);
        EXPECT_MODIFIED(merged, {interval_3minus_3, interval_2_4});
      }
    }
    WHEN("merging {-3, -1} with {-4, -2}")
    {
      auto op1 = make_value_set({val3minus, val1minus}, environment, ns);
      auto op2 = make_value_set({val4minus, val2minus}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen lower bound - {[-8, -4], -3, -2, -1}")
      {
        EXPECT_MODIFIED(
          merged,
          {constant_interval_exprt(val8minus, val4minus),
           val3minus,
           val2minus,
           val1minus});
      }
    }
    WHEN("merging {[-3, -1]} with {[-4, -2]}")
    {
      auto interval31minus = constant_interval_exprt(val3minus, val1minus);
      auto interval42minus = constant_interval_exprt(val4minus, val2minus);
      auto op1 = make_value_set(interval31minus, environment, ns);
      auto op2 = make_value_set(interval42minus, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen lower bound - {[-8, -2], [-3, -1]}")
      {
        EXPECT_MODIFIED(
          merged,
          {constant_interval_exprt(val8minus, val2minus), interval31minus});
      }
    }
    WHEN("merging {-3, -1} with {[-4, -2]}")
    {
      auto interval42minus = constant_interval_exprt(val4minus, val2minus);
      auto op1 = make_value_set({val3minus, val1minus}, environment, ns);
      auto op2 = make_value_set(interval42minus, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen lower bound - {[-8, -2], -1}")
      {
        EXPECT_MODIFIED(
          merged, {constant_interval_exprt(val8minus, val2minus), val1minus});
      }
    }
    WHEN("merging {[-3, -1]} with {-4, -2}")
    {
      auto interval31minus = constant_interval_exprt(val3minus, val1minus);
      auto op1 = make_value_set(interval31minus, environment, ns);
      auto op2 = make_value_set({val4minus, val2minus}, environment, ns);

      auto merged = widening_merge(op1, op2);
      THEN("widen lower bound - {[-8, -4], [-3, -1], -2}")
      {
        EXPECT_MODIFIED(
          merged,
          {constant_interval_exprt(val8minus, val4minus),
           interval31minus,
           val2minus});
      }
    }

    WHEN("merging {0, very_large} with {-very_large, 0}")
    {
      auto op1 = make_value_set({val0, veryLarge}, environment, ns);
      auto op2 = make_value_set({veryLargeMinus, val0}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is {[MIN, -very_large], 0, very_large]")
      {
        EXPECT_MODIFIED(
          merged,
          {constant_interval_exprt(valMin, veryLargeMinus), val0, veryLarge});
      }
    }
    WHEN("merging {-very_large, 0} with {0, very_large}")
    {
      auto op1 = make_value_set({veryLargeMinus, val0}, environment, ns);
      auto op2 = make_value_set({val0, veryLarge}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is {-very_large, 0, [very_large, MAX]}")
      {
        EXPECT_MODIFIED(
          merged,
          {veryLargeMinus, val0, constant_interval_exprt(veryLarge, valMax)});
      }
    }

    WHEN("merging {-very_large, very_large } with {0, 1}")
    {
      auto op1 = make_value_set({veryLargeMinus, veryLarge}, environment, ns);
      auto op2 = make_value_set({val0, val1}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is {-very_large, val0, val1, very_large}")
      {
        EXPECT_MODIFIED(merged, {veryLargeMinus, val0, val1, veryLarge});
      }
    }
    WHEN("merging {0, 1} with {-very_large, very_large}")
    {
      auto op1 = make_value_set({val0, val1}, environment, ns);
      auto op2 = make_value_set({veryLargeMinus, veryLarge}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is {[MIN, 0}, [1, MAX]}")
      {
        EXPECT_MODIFIED(
          merged,
          {constant_interval_exprt(valMin, veryLargeMinus),
           val0,
           val1,
           constant_interval_exprt(veryLarge, valMax)});
      }
    }
  }
}
