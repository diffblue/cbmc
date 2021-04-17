/*******************************************************************\

 Module: Unit tests for constant_abstract_valuet::meet

 Author: Jez Higgins.

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>

static std::shared_ptr<const constant_abstract_valuet>
meet(abstract_object_pointert const &op1, abstract_object_pointert const &op2)
{
  auto result = abstract_objectt::meet(op1, op2);
  return as_constant(result.object);
}

static void THEN_BOTTOM(std::shared_ptr<const constant_abstract_valuet> &result)
{
  THEN("result is BOTTOM")
  {
    EXPECT_BOTTOM(result);
  }
}

static void THEN_TOP(std::shared_ptr<const constant_abstract_valuet> &result)
{
  THEN("result is TOP")
  {
    EXPECT_TOP(result);
  }
}

static void THEN_ONE(std::shared_ptr<const constant_abstract_valuet> &result)
{
  THEN("result is 1")
  {
    const typet type = signedbv_typet(32);
    const exprt val1 = from_integer(1, type);
    EXPECT(result, val1);
  }
}

SCENARIO(
  "meet constant_abstract_value",
  "[core][analyses][variable-sensitivity][constant_abstract_value][meet]")
{
  const typet type = signedbv_typet(32);
  const exprt val0 = from_integer(0, type);
  const exprt val1 = from_integer(1, type);
  const exprt val2 = from_integer(2, type);

  auto config = vsd_configt::constant_domain();
  config.context_tracking.data_dependency_context = false;
  config.context_tracking.last_write_context = false;
  auto object_factory =
    variable_sensitivity_object_factoryt::configured_with(config);
  abstract_environmentt environment{object_factory};
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("meeting two constants")
  {
    WHEN("meeting 1 with 1")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting 1 with 2")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_constant(val2, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting 1 with TOP")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto top2 = make_top_constant();

      auto result = meet(op1, top2);

      THEN_ONE(result);
    }
    WHEN("meeting 1 with BOTTOM")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto bottom2 = make_bottom_constant();

      auto result = meet(op1, bottom2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting TOP with 1")
    {
      auto top1 = make_top_constant();
      auto op2 = make_constant(val1, environment, ns);

      auto result = meet(top1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting TOP with TOP")
    {
      auto top1 = make_top_constant();
      auto top2 = make_top_constant();

      auto result = meet(top1, top2);

      THEN_TOP(result);
    }
    WHEN("meeting TOP with BOTTOM")
    {
      auto top1 = make_top_constant();
      auto bottom2 = make_bottom_constant();

      auto result = meet(top1, bottom2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting BOTTOM with 1")
    {
      auto bottom1 = make_bottom_constant();
      auto op2 = make_constant(val1, environment, ns);

      auto result = meet(bottom1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting BOTTOM with TOP")
    {
      auto bottom1 = make_bottom_constant();
      auto top2 = make_top_constant();

      auto result = meet(bottom1, top2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting BOTTOM with BOTTOM")
    {
      auto bottom1 = make_bottom_constant();
      auto bottom2 = make_bottom_constant();

      auto result = meet(bottom1, bottom2);

      THEN_BOTTOM(result);
    }
  }

  GIVEN("meeting a constant and an interval")
  {
    WHEN("meeting 1 with [1, 1]")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_interval(val1, val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting 1 with [1, 2]")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_interval(val1, val2, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting 1 with [0, 2]")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_interval(val0, val2, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting 1 with [2, 2]")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_interval(val2, val2, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting BOTTOM with [1, 1]")
    {
      auto op1 = make_bottom_constant();
      auto op2 = make_interval(val1, val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting BOTTOM with [1, 2]")
    {
      auto op1 = make_bottom_constant();
      auto op2 = make_interval(val1, val2, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
  }

  GIVEN("meeting a constant and a value set")
  {
    WHEN("meeting 1 with { 1 }")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting 1 with { 2 }")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_value_set(val2, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting 1 with { 1, 2 }")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting 1 with { 0, 2 }")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_value_set({val0, val2}, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting 1 with { [ 1, 1 ] }")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 =
        make_value_set(constant_interval_exprt(val1, val1), environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting 1 with { 1, [1, 1] }")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_value_set(
        {val1, constant_interval_exprt(val1, val1)}, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting 1 with { [ 2, 2 ] }")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 =
        make_value_set(constant_interval_exprt(val2, val2), environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting 1 with { [ 1, 2 ] }")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 =
        make_value_set(constant_interval_exprt(val1, val2), environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting 1 with { 1, [ 1, 2 ] }")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_value_set(
        {val1, constant_interval_exprt(val1, val2)}, environment, ns);

      auto result = meet(op1, op2);

      THEN_ONE(result);
    }
    WHEN("meeting BOTTOM with { 1 }")
    {
      auto op1 = make_bottom_constant();
      auto op2 = make_value_set(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting BOTTOM with { 1, 2 }")
    {
      auto op1 = make_bottom_constant();
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting BOTTOM with { [ 1, 1 ] }")
    {
      auto op1 = make_bottom_constant();
      auto op2 =
        make_value_set(constant_interval_exprt(val1, val1), environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting BOTTOM with { [ 1, 2 ] }")
    {
      auto op1 = make_bottom_constant();
      auto op2 =
        make_value_set(constant_interval_exprt(val1, val2), environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting BOTTOM with { 1, [ 1, 2 ] }")
    {
      auto op1 = make_bottom_constant();
      auto op2 = make_value_set(
        {val1, constant_interval_exprt(val1, val2)}, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
  }
}
