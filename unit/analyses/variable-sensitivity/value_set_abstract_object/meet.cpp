/*******************************************************************\

 Module: meet unit tests for value_set_abstract_objectt::meet

 Author: Jez Higgins

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/interval_abstract_value.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>

#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/symbol_table.h>

static std::shared_ptr<const value_set_abstract_objectt>
meet(abstract_object_pointert const &op1, abstract_object_pointert const &op2)
{
  auto result = abstract_objectt::meet(op1, op2);
  return as_value_set(result.object);
}

static void
THEN_BOTTOM(std::shared_ptr<const value_set_abstract_objectt> &result)
{
  THEN("result is BOTTOM")
  {
    EXPECT_BOTTOM(result);
  }
}

static void THEN_TOP(std::shared_ptr<const value_set_abstract_objectt> &result)
{
  THEN("result is TOP")
  {
    EXPECT_TOP(result);
  }
}

static void THEN_VALUE_SET(
  std::shared_ptr<const value_set_abstract_objectt> &result,
  const std::vector<exprt> &expected_values)
{
  THEN("result is " + exprs_to_str(expected_values))
  {
    EXPECT(result, expected_values);
  }
}

SCENARIO(
  "meet value_set_abstract_objectt",
  "[core][analyses][variable-sensitivity][value_set_abstract_object][meet]")
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
  auto interval_1_2 = constant_interval_exprt(val1, val2);
  auto interval_1_3 = constant_interval_exprt(val1, val3);

  auto object_factory = variable_sensitivity_object_factoryt::configured_with(
    vsd_configt::intervals());

  abstract_environmentt environment{object_factory};
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("meeting two value_sets")
  {
    WHEN("meeting { 1 } with { 1 }")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_VALUE_SET(result, {val1});
    }
    WHEN("meeting { 1 } with { 2 }")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_value_set(val2, environment, ns);

      auto result = meet(op1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting { 1, 2, 3 } with { 1 }")
    {
      auto op1 = make_value_set({val1, val2, val3}, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_VALUE_SET(result, {val1});
    }
    WHEN("meeting { 1, 2, 3 } with { 1, 2 }")
    {
      auto op1 = make_value_set({val1, val2, val3}, environment, ns);
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto result = meet(op1, op2);

      THEN_VALUE_SET(result, {interval_1_2});
    }
    WHEN("meeting { [1, 2], 3 } with { 1, 2 }")
    {
      auto op1 = make_value_set({interval_1_2, val3}, environment, ns);
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto result = meet(op1, op2);

      THEN_VALUE_SET(result, {interval_1_2});
    }
    WHEN("meeting { 1 } with { 1, 2, 3 }")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_value_set({val1, val2, val3}, environment, ns);

      auto result = meet(op1, op2);

      THEN_VALUE_SET(result, {val1});
    }
    WHEN("meeting { [1, 3] } with { 1 }")
    {
      auto op1 = make_value_set(interval_1_3, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);

      auto result = meet(op1, op2);

      THEN_VALUE_SET(result, {val1});
    }
    WHEN("meeting { 1 } with { [1, 3] }")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_value_set(interval_1_3, environment, ns);

      auto result = meet(op1, op2);

      THEN_VALUE_SET(result, {val1});
    }
    WHEN("meeting { 1, 2 } with TOP")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto top2 = make_top_value_set();

      auto result = meet(op1, top2);

      THEN_VALUE_SET(result, {val1, val2});
    }
    WHEN("meeting { 1, 2 } with BOTTOM")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto top2 = make_bottom_value_set();

      auto result = meet(op1, top2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting TOP with { 1, 2 }")
    {
      auto top1 = make_top_value_set();
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto result = meet(top1, op2);

      THEN_VALUE_SET(result, {val1, val2});
    }
    WHEN("meeting TOP with TOP")
    {
      auto top1 = make_top_value_set();
      auto top2 = make_top_value_set();

      auto result = meet(top1, top2);

      THEN_TOP(result);
    }
    WHEN("meeting TOP with BOTTOM")
    {
      auto top1 = make_top_value_set();
      auto bottom2 = make_bottom_value_set();

      auto result = meet(top1, bottom2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting BOTTOM with { 1, 2 }")
    {
      auto bottom1 = make_bottom_value_set();
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto result = meet(bottom1, op2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting BOTTOM with TOP")
    {
      auto bottom1 = make_bottom_value_set();
      auto top2 = make_top_value_set();

      auto result = meet(bottom1, top2);

      THEN_BOTTOM(result);
    }
    WHEN("meeting BOTTOM with BOTTOM")
    {
      auto bottom1 = make_bottom_value_set();
      auto bottom2 = make_bottom_value_set();

      auto result = meet(bottom1, bottom2);

      THEN_BOTTOM(result);
    }
  }
}
