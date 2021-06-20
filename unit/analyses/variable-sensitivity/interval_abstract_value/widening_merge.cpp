/*******************************************************************\

 Module: Unit tests for interval_abstract_valuet::merge

 Author: Jez Higgins.

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>

static merge_result<const interval_abstract_valuet> widening_merge(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2)
{
  auto result = abstract_objectt::merge(op1, op2, widen_modet::could_widen);

  return {result.modified, as_interval(result.object)};
}

SCENARIO(
  "widening merge interval_abstract_value",
  "[core][analyses][variable-sensitivity][interval_abstract_value][merge]")
{
  const typet type = signedbv_typet(32);
  const exprt val0 = from_integer(0, type);
  const exprt val1 = from_integer(1, type);
  const exprt val2 = from_integer(2, type);
  const exprt val3 = from_integer(3, type);
  const exprt val4 = from_integer(4, type);
  const exprt val5 = from_integer(5, type);
  const exprt val8 = from_integer(8, type);
  const exprt val10 = from_integer(10, type);
  const exprt val1minus = from_integer(-1, type);
  const exprt val2minus = from_integer(-2, type);
  const exprt val3minus = from_integer(-3, type);
  const exprt val4minus = from_integer(-4, type);
  const exprt val5minus = from_integer(-5, type);
  const exprt val8minus = from_integer(-8, type);
  const exprt val10minus = from_integer(-10, type);
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

  GIVEN("interval merges which don't widen")
  {
    WHEN("merging [1, 2] with [1, 2]")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_interval(val1, val2, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is unmodified [1, 2]")
      {
        EXPECT_UNMODIFIED(merged, val1, val2);
      }
    }
    WHEN("merging [1, 5] with [2, 3]")
    {
      auto op1 = make_interval(val1, val5, environment, ns);
      auto op2 = make_interval(val2, val3, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is unmodified [1, 5]")
      {
        EXPECT_UNMODIFIED(merged, val1, val5);
      }
    }
  }

  GIVEN("widening merges with TOP or BOTTOM")
  {
    WHEN("merging [1, 2] with TOP")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto top2 = make_top_interval();

      auto merged = widening_merge(op1, top2);

      THEN("result is modified TOP")
      {
        EXPECT_MODIFIED_TOP(merged);
      }
    }
    WHEN("merging [1, 2] with BOTTOM")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto bottom2 = make_bottom_interval();

      auto merged = widening_merge(op1, bottom2);

      THEN("result is unmodified [1, 2]")
      {
        EXPECT_UNMODIFIED(merged, val1, val2);
      }
    }
    WHEN("merging TOP with [1, 2]")
    {
      auto top1 = make_top_interval();
      auto op2 = make_interval(val1, val2, environment, ns);

      auto merged = widening_merge(top1, op2);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED_TOP(merged);
      }
    }
    WHEN("merging BOTTOM with [1, 2]")
    {
      auto bottom1 = make_bottom_interval();
      auto op2 = make_interval(val1, val2, environment, ns);

      auto merged = widening_merge(bottom1, op2);

      THEN("result is modified [1, 2]")
      {
        EXPECT_MODIFIED(merged, val1, val2);
      }
    }
    WHEN("merging TOP with TOP")
    {
      auto top1 = make_top_interval();
      auto top2 = make_top_interval();

      auto merged = widening_merge(top1, top2);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED_TOP(merged);
      }
    }
    WHEN("merging TOP with BOTTOM")
    {
      auto top1 = make_top_interval();
      auto bottom2 = make_bottom_interval();

      auto merged = widening_merge(top1, bottom2);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED_TOP(merged);
      }
    }
    WHEN("merging BOTTOM with TOP")
    {
      auto bottom1 = make_bottom_interval();
      auto top2 = make_top_interval();

      auto merged = widening_merge(bottom1, top2);

      THEN("result is modified TOP")
      {
        EXPECT_MODIFIED_TOP(merged);
      }
    }
    WHEN("merging BOTTOM with BOTTOM")
    {
      auto bottom1 = make_bottom_interval();
      auto bottom2 = make_bottom_interval();

      auto merged = widening_merge(bottom1, bottom2);

      THEN("result is unmodified BOTTOM")
      {
        EXPECT_UNMODIFIED_BOTTOM(merged);
      }
    }
  }

  GIVEN("interval merges which do widen")
  {
    WHEN("merging [1, 3] with [2, 4]")
    {
      auto op1 = make_interval(val1, val3, environment, ns);
      auto op2 = make_interval(val2, val4, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen upper bound - [1, 8]")
      {
        EXPECT_MODIFIED(merged, val1, val8);
      }
    }
    WHEN("merging [2, 4] with [1, 3]")
    {
      auto op1 = make_interval(val2, val4, environment, ns);
      auto op2 = make_interval(val1, val3, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen lower bound - [-3, 4]")
      {
        EXPECT_MODIFIED(merged, val3minus, val4);
      }
    }
    WHEN("merging [1, 2] with [4, 5]")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_interval(val4, val5, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen upper bound - [1, 10]")
      {
        EXPECT_MODIFIED(merged, val1, val10);
      }
    }
    WHEN("merging [4, 5] with [1, 2]")
    {
      auto op1 = make_interval(val4, val5, environment, ns);
      auto op2 = make_interval(val1, val2, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen lower bound - [-4, 5]")
      {
        EXPECT_MODIFIED(merged, val4minus, val5);
      }
    }
    WHEN("merging [2, 3] with [1, 5]")
    {
      auto op1 = make_interval(val2, val3, environment, ns);
      auto op2 = make_interval(val1, val5, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is widen both bounds - [-4, 10]")
      {
        EXPECT_MODIFIED(merged, val4minus, val10);
      }
    }
    WHEN("merging [-3, -1] with [-4, -2]")
    {
      auto op1 = make_interval(val3minus, val1minus, environment, ns);
      auto op2 = make_interval(val4minus, val2minus, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen lower bound - [-8, -1]")
      {
        EXPECT_MODIFIED(merged, val8minus, val1minus);
      }
    }
    WHEN("merging [-4, -2] with [-3, -1]")
    {
      auto op1 = make_interval(val4minus, val2minus, environment, ns);
      auto op2 = make_interval(val3minus, val1minus, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen upper bound - [-4, 3]")
      {
        EXPECT_MODIFIED(merged, val4minus, val3);
      }
    }
    WHEN("merging [-2, -1] with [-5, -4]")
    {
      auto op1 = make_interval(val2minus, val1minus, environment, ns);
      auto op2 = make_interval(val5minus, val4minus, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen lower bound - [-10, -1]")
      {
        EXPECT_MODIFIED(merged, val10minus, val1minus);
      }
    }
    WHEN("merging [-5, -4] with [-2, -1]")
    {
      auto op1 = make_interval(val5minus, val4minus, environment, ns);
      auto op2 = make_interval(val2minus, val1minus, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("widen upper bound - [-5, 4]")
      {
        EXPECT_MODIFIED(merged, val5minus, val4);
      }
    }
    WHEN("merging [-3, -2] with [-5, -1]")
    {
      auto op1 = make_interval(val3minus, val2minus, environment, ns);
      auto op2 = make_interval(val5minus, val1minus, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is widen both bounds - [-10, 4]")
      {
        EXPECT_MODIFIED(merged, val10minus, val4);
      }
    }

    WHEN("merging [1, 10] with [1, MAX]")
    {
      auto op1 = make_interval(val1, val10, environment, ns);
      auto op2 = make_interval(val1, valMax, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is [1, MAX]")
      {
        EXPECT_MODIFIED(merged, val1, valMax);
      }
    }
    WHEN("merging [0, 1] with [1, very_large]")
    {
      auto op1 = make_interval(val0, val1, environment, ns);
      auto op2 = make_interval(val1, veryLarge, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is [0, MAX]")
      {
        EXPECT_MODIFIED(merged, val0, valMax);
      }
    }
    WHEN("merging [0, 1] with [1, unsigned_very_large]")
    {
      auto utype = unsignedbv_typet(32);
      auto uval0 = from_integer(0, utype);
      auto uval1 = from_integer(1, utype);
      auto uVeryLarge = from_integer(2 << 30, utype);

      auto op1 = make_interval(uval0, uval1, environment, ns);
      auto op2 = make_interval(uval1, uVeryLarge, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is [0, MAX]")
      {
        auto uvalMax = max_exprt(utype);
        EXPECT_MODIFIED(merged, uval0, uvalMax);
      }
    }
    WHEN("merging unsigned [7, 9] with [3, 6]")
    {
      auto utype = unsignedbv_typet(32);
      auto uval0 = from_integer(0, utype);
      auto uval3 = from_integer(3, utype);
      auto uval6 = from_integer(6, utype);
      auto uval7 = from_integer(7, utype);
      auto uval9 = from_integer(9, utype);

      auto op1 = make_interval(uval7, uval9, environment, ns);
      auto op2 = make_interval(uval3, uval6, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is [0, 9]")
      {
        EXPECT_MODIFIED(merged, uval0, uval9);
      }
    }

    WHEN("merging [1, 10] with [MIN, 1]")
    {
      auto op1 = make_interval(val1, val10, environment, ns);
      auto op2 = make_interval(valMin, val1, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is [MIN, 10]")
      {
        EXPECT_MODIFIED(merged, valMin, val10);
      }
    }
    WHEN("merging [0, 1] with [-very_large, 1]")
    {
      auto op1 = make_interval(val0, val1, environment, ns);
      auto op2 = make_interval(veryLargeMinus, val1, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is [MIN, 1]")
      {
        EXPECT_MODIFIED(merged, valMin, val1);
      }
    }

    WHEN("merging [1, MAX] with [MIN, 1]")
    {
      auto op1 = make_interval(val1, valMax, environment, ns);
      auto op2 = make_interval(valMin, val1, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is TOP - ie [MIN, MAX]")
      {
        EXPECT_MODIFIED_TOP(merged);
      }
    }
    WHEN("merging [MIN, 1] with [1, MAX]")
    {
      auto op1 = make_interval(valMin, val1, environment, ns);
      auto op2 = make_interval(val1, valMax, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is TOP - ie [MIN, MAX]")
      {
        EXPECT_MODIFIED_TOP(merged);
      }
    }
    WHEN("merging [0, very_large] with [-very_large, 0]")
    {
      auto op1 = make_interval(val0, veryLarge, environment, ns);
      auto op2 = make_interval(veryLargeMinus, val0, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is [MIN, very_large]")
      {
        EXPECT_MODIFIED(merged, valMin, veryLarge);
      }
    }
    WHEN("merging [-very_large, 0] with [0, very_large]")
    {
      auto op1 = make_interval(veryLargeMinus, val0, environment, ns);
      auto op2 = make_interval(val0, veryLarge, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is [-very_large, MAX]")
      {
        EXPECT_MODIFIED(merged, veryLargeMinus, valMax);
      }
    }

    WHEN("merging [-very_large, very_large] with [0, 1]")
    {
      auto op1 = make_interval(veryLargeMinus, veryLarge, environment, ns);
      auto op2 = make_interval(val0, val1, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is [-very_large, very_large]")
      {
        EXPECT_UNMODIFIED(merged, veryLargeMinus, veryLarge);
      }
    }
    WHEN("merging [0, 1] with [-very_large, very_large]")
    {
      auto op1 = make_interval(val0, val1, environment, ns);
      auto op2 = make_interval(veryLargeMinus, veryLarge, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is TOP, ie [MIN, MAX]")
      {
        EXPECT_MODIFIED_TOP(merged);
      }
    }
  }
}
