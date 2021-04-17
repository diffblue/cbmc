/*******************************************************************\

 Module: Unit tests for interval_abstract_valuet::meet

 Author: DiffBlue Limited.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/interval_abstract_value.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>

#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <util/arith_tools.h>
#include <util/bitvector_types.h>

static std::shared_ptr<const interval_abstract_valuet>
meet(abstract_object_pointert const &op1, abstract_object_pointert const &op2)
{
  auto result = abstract_objectt::meet(op1, op2);
  return as_interval(result.object);
}

static void THEN_BOTTOM(std::shared_ptr<const interval_abstract_valuet> &result)
{
  THEN("result is BOTTOM")
  {
    EXPECT_BOTTOM(result);
  }
}

static void THEN_TOP(std::shared_ptr<const interval_abstract_valuet> &result)
{
  THEN("result is TOP")
  {
    EXPECT_TOP(result);
  }
}

static void THEN_INTERVAL(
  std::shared_ptr<const interval_abstract_valuet> &result,
  exprt lower,
  exprt upper)
{
  THEN("result is [" + expr_to_str(lower) + ", " + expr_to_str(upper) + "]")
  {
    EXPECT(result, lower, upper);
  }
}

static void THEN_ONE(std::shared_ptr<const interval_abstract_valuet> &result)
{
  const typet type = signedbv_typet(32);
  const exprt val1 = from_integer(1, type);
  THEN_INTERVAL(result, val1, val1);
}

SCENARIO(
  "meet interval_abstract_valuet",
  "[core][analyses][variable-sensitivity][interval_abstract_value][meet]")
{
  const typet type = signedbv_typet(32);
  const exprt val0 = from_integer(0, type);
  const exprt val1 = from_integer(1, type);
  const exprt val2 = from_integer(2, type);
  const exprt val3 = from_integer(3, type);
  const exprt val5 = from_integer(5, type);
  const exprt val10 = from_integer(10, type);
  const exprt val11 = from_integer(11, type);
  const exprt val15 = from_integer(15, type);

  auto object_factory = variable_sensitivity_object_factoryt::configured_with(
    vsd_configt::intervals());

  abstract_environmentt environment{object_factory};
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("meeting two intervals")
  {
    const auto varx = symbol_exprt(type);
    const auto x_le_10 = binary_relation_exprt(varx, ID_le, val10);
    const auto lt_10_x = binary_relation_exprt(val10, ID_lt, varx);
    const auto x_ge_5 = binary_relation_exprt(varx, ID_ge, val5);

    const auto max_value = signedbv_typet(32).largest_expr();
    const auto x_ge_max = binary_relation_exprt(varx, ID_ge, max_value);
    const auto x_gt_max = binary_relation_exprt(varx, ID_gt, max_value);

    WHEN("meeting [1, 10] with [1, 10]")
    {
      auto op1 = make_interval(val1, val10, environment, ns);
      auto op2 = make_interval(val1, val10, environment, ns);

      auto result = meet(op1, op2);

      THEN_INTERVAL(result, val1, val10);
    }
    WHEN("meeting [1, 2] with [10, 15]")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_interval(val10, val15, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting [10, 15] with [1, 2]")
    {
      auto op1 = make_interval(val10, val15, environment, ns);
      auto op2 = make_interval(val1, val2, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting [1, 10] with [2, 15]")
    {
      auto op1 = make_interval(val1, val10, environment, ns);
      auto op2 = make_interval(val2, val15, environment, ns);

      auto result = meet(op1, op2);

      THEN_INTERVAL(result, val2, val10);
    }
    WHEN("meeting [2, 15] with [1, 10]")
    {
      auto op1 = make_interval(val2, val15, environment, ns);
      auto op2 = make_interval(val1, val10, environment, ns);

      auto result = meet(op1, op2);

      THEN_INTERVAL(result, val2, val10);
    }
    WHEN("meeting [x <= 10] with [2, 15]")
    {
      auto op1 = make_interval(x_le_10, environment, ns);
      auto op2 = make_interval(val2, val15, environment, ns);

      auto result = meet(op1, op2);

      THEN_INTERVAL(result, val2, val10);
    }
    WHEN("meeting [2, 15] with [x <= 10]")
    {
      auto op1 = make_interval(val2, val15, environment, ns);
      auto op2 = make_interval(x_le_10, environment, ns);

      auto result = meet(op1, op2);

      THEN_INTERVAL(result, val2, val10);
    }
    WHEN("meeting [10 < x] with [2, 15]")
    {
      auto op1 = make_interval(lt_10_x, environment, ns);
      auto op2 = make_interval(val2, val15, environment, ns);

      auto result = meet(op1, op2);

      THEN_INTERVAL(result, val11, val15);
    }
    WHEN("meeting [2, 15] with [10 < x]")
    {
      auto op1 = make_interval(val2, val15, environment, ns);
      auto op2 = make_interval(lt_10_x, environment, ns);

      auto result = meet(op1, op2);

      THEN_INTERVAL(result, val11, val15);
    }
    WHEN("meeting [10 < x] with [x >= max]")
    {
      auto op1 = make_interval(lt_10_x, environment, ns);
      auto op2 = make_interval(x_ge_max, environment, ns);

      auto result = meet(op1, op2);

      THEN_INTERVAL(result, max_value, max_exprt(max_value.type()));
    }
    WHEN("meeting [x >= max] with [10 < x]")
    {
      auto op1 = make_interval(x_ge_max, environment, ns);
      auto op2 = make_interval(lt_10_x, environment, ns);

      auto result = meet(op1, op2);

      THEN_INTERVAL(result, max_value, max_exprt(max_value.type()));
    }
    WHEN("meeting [x <= 10] with [x > max]")
    {
      auto op1 = make_interval(lt_10_x, environment, ns);
      auto op2 = make_interval(x_gt_max, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting [x > max] with [x <= 10]")
    {
      auto op1 = make_interval(x_gt_max, environment, ns);
      auto op2 = make_interval(lt_10_x, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting [x <= 10] with [x >= 5]")
    {
      auto op1 = make_interval(x_le_10, environment, ns);
      auto op2 = make_interval(x_ge_5, environment, ns);

      auto result = meet(op1, op2);

      THEN_INTERVAL(result, val5, val10);
    }
    WHEN("meeting [x >= 5] with [x <= 10]")
    {
      auto op1 = make_interval(x_ge_5, environment, ns);
      auto op2 = make_interval(x_le_10, environment, ns);

      auto result = meet(op1, op2);

      THEN_INTERVAL(result, val5, val10);
    }
    WHEN("meeting [1, 2] with TOP")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto top2 = make_top_interval();

      auto result = meet(op1, top2);

      THEN_INTERVAL(result, val1, val2);
    }
    WHEN("meeting [1, 2] with BOTTOM")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto bottom2 = make_bottom_interval();

      auto result = meet(op1, bottom2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting TOP with [1, 2]")
    {
      auto top1 = make_top_interval();
      auto op2 = make_interval(val1, val2, environment, ns);

      auto result = meet(top1, op2);

      THEN_INTERVAL(result, val1, val2);
    }
    WHEN("meeting TOP with TOP")
    {
      auto top1 = make_top_interval();
      auto top2 = make_top_interval();

      auto result = meet(top1, top2);

      THEN_TOP(result);
    }
    WHEN("meeting TOP with BOTTOM")
    {
      auto top1 = make_top_interval();
      auto bottom2 = make_bottom_interval();

      auto result = meet(top1, bottom2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting BOTTOM with [1, 2]")
    {
      auto bottom1 = make_bottom_interval();
      auto op2 = make_interval(val1, val2, environment, ns);

      auto result = meet(bottom1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting BOTTOM with TOP")
    {
      auto bottom1 = make_bottom_interval();
      auto top2 = make_top_interval();

      auto result = meet(bottom1, top2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting BOTTOM with BOTTOM")
    {
      auto bottom1 = make_bottom_interval();
      auto bottom2 = make_bottom_interval();

      auto result = meet(bottom1, bottom2);

      THEN_BOTTOM(result);
    }
  }
  GIVEN("meeting an interval and a constant")
  {
    WHEN("meeting [0, 1] with 1")
    {
      auto op1 = make_interval(val0, val1, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting [1, 1] with 1")
    {
      auto op1 = make_interval(val1, val1, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting [1, 2] with 1")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting [0, 2] with 1")
    {
      auto op1 = make_interval(val0, val2, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting [2, 5] with 1")
    {
      auto op1 = make_interval(val2, val5, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting BOTTOM with 1")
    {
      auto op1 = make_bottom_interval();
      auto op2 = make_constant(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
  }
  GIVEN("meeting an interval and a value set")
  {
    WHEN("meeting [0, 1] with { 1 }")
    {
      auto op1 = make_interval(val0, val1, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting [1, 1] with { 1 }")
    {
      auto op1 = make_interval(val1, val1, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting [1, 2] with { 1 }")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting [0, 2] with { 1 }")
    {
      auto op1 = make_interval(val0, val2, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting [2, 5] with { 1 }")
    {
      auto op1 = make_interval(val2, val5, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting [2, 5] with { 1, 2, 3 }")
    {
      auto op1 = make_interval(val2, val5, environment, ns);
      auto op2 = make_value_set({val1, val2, val3}, environment, ns);

      auto result = meet(op1, op2);

      THEN_INTERVAL(result, val2, val3);
    }
    WHEN("meeting [2, 5] with { 1, 3 }")
    {
      auto op1 = make_interval(val2, val5, environment, ns);
      auto op2 = make_value_set({val1, val3}, environment, ns);

      auto result = meet(op1, op2);

      THEN_INTERVAL(result, val2, val3);
    }
    WHEN("meeting [2, 5] with { 1, 3, 5 10 }")
    {
      auto op1 = make_interval(val2, val5, environment, ns);
      auto op2 = make_value_set({val1, val3, val5, val10}, environment, ns);

      auto result = meet(op1, op2);

      THEN_INTERVAL(result, val2, val5);
    }
    WHEN("meeting [2, 5] with { [1, 3] }")
    {
      auto op1 = make_interval(val2, val5, environment, ns);
      auto op2 =
        make_value_set(constant_interval_exprt(val1, val3), environment, ns);

      auto result = meet(op1, op2);

      THEN_INTERVAL(result, val2, val3);
    }
    WHEN("meeting BOTTOM with { 1 }")
    {
      auto op1 = make_bottom_interval();
      auto op2 = make_value_set(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
  }
}
