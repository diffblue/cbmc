/*******************************************************************\

 Module: Unit tests for abstract_value_objectt::expression_transform

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>

SCENARIO(
  "value expression evaluation",
  "[core][analyses][variable-sensitivity][constant_abstract_value][value_set_"
  "abstract_object][interval_abstract_value][expression_transform]")
{
  const typet type = signedbv_typet(32);
  const exprt val1 = from_integer(1, type);
  const exprt val2 = from_integer(2, type);
  const exprt val3 = from_integer(3, type);
  const exprt val4 = from_integer(4, type);
  const exprt val5 = from_integer(5, type);

  auto config = vsd_configt::constant_domain();
  config.context_tracking.data_dependency_context = false;
  config.context_tracking.last_write_context = false;
  auto object_factory =
    variable_sensitivity_object_factoryt::configured_with(config);
  abstract_environmentt environment{object_factory};
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("adding two constants")
  {
    WHEN("1 + 2")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_constant(val2, environment, ns);
      auto result = add_as_constant(op1, op2, environment, ns);

      THEN("= 3")
      {
        EXPECT(result, val3);
      }
    }
  }
  GIVEN("adding a constant and TOP")
  {
    WHEN("1 + TOP constant")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_top_constant();
      auto result = add_as_constant(op1, op2, environment, ns);

      THEN("= TOP")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("1 + TOP interval")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_top_interval();
      auto result = add_as_constant(op1, op2, environment, ns);

      THEN("= TOP")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("1 + TOP value_set")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_top_value_set();
      auto result = add_as_constant(op1, op2, environment, ns);

      THEN("= TOP")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("TOP constant + 1")
    {
      auto op1 = make_top_constant();
      auto op2 = make_constant(val1, environment, ns);
      auto result = add_as_constant(op1, op2, environment, ns);

      THEN("= TOP")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("TOP interval + 1")
    {
      auto op1 = make_top_interval();
      auto op2 = make_constant(val1, environment, ns);
      auto result = add_as_constant(op1, op2, environment, ns);

      THEN("= TOP")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("TOP value_set + 1")
    {
      auto op1 = make_top_value_set();
      auto op2 = make_constant(val1, environment, ns);
      auto result = add_as_constant(op1, op2, environment, ns);

      THEN("= TOP")
      {
        EXPECT_TOP(result);
      }
    }
  }
  GIVEN("adding a constant and an interval")
  {
    WHEN("1 + [2,2]")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_interval(val2, val2, environment, ns);
      auto result = add_as_interval(op1, op2, environment, ns);

      THEN("= [3,3]")
      {
        EXPECT(result, val3, val3);
      }
    }
    WHEN("1 + [2,4]")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_interval(val2, val4, environment, ns);
      auto result = add_as_interval(op1, op2, environment, ns);

      THEN("= [3,5]")
      {
        EXPECT(result, val3, val5);
      }
    }
  }
  GIVEN("adding a constant and a value set")
  {
    WHEN("1 + { 2 }")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_value_set(val2, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { 3 }")
      {
        EXPECT(result, {val3});
      }
    }
    WHEN("1 + { 2, 3, 4 }")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_value_set({val2, val3, val4}, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { 3, 4, 5 }")
      {
        EXPECT(result, {val3, val4, val5});
      }
    }
  }

  GIVEN("adding two intervals")
  {
    WHEN("[1,1] + [2,2]")
    {
      auto op1 = make_interval(val1, val1, environment, ns);
      auto op2 = make_interval(val2, val2, environment, ns);
      auto result = add_as_interval(op1, op2, environment, ns);

      THEN("= [3,3]")
      {
        EXPECT(result, val3, val3);
      }
    }
    WHEN("[1,2] + [1,2]")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_interval(val1, val2, environment, ns);
      auto result = add_as_interval(op1, op2, environment, ns);

      THEN("= [2,4]")
      {
        EXPECT(result, val2, val4);
      }
    }
  }
  GIVEN("adding an interval and TOP")
  {
    WHEN("[1,2] + TOP constant")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_top_constant();
      auto result = add(op1, op2, environment, ns);

      THEN("= TOP")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("[1,2] + TOP interval")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_top_interval();
      auto result = add(op1, op2, environment, ns);

      THEN("= TOP")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("[1,2] + TOP value_set")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_top_value_set();
      auto result = add(op1, op2, environment, ns);

      THEN("= TOP")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("TOP constant + [1,2]")
    {
      auto op1 = make_top_constant();
      auto op2 = make_interval(val1, val2, environment, ns);
      auto result = add(op1, op2, environment, ns);

      THEN("= TOP")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("TOP interval + [1,2]")
    {
      auto op1 = make_top_interval();
      auto op2 = make_interval(val1, val2, environment, ns);
      auto result = add(op1, op2, environment, ns);

      THEN("= TOP")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("TOP value_set + [1,2]")
    {
      auto op1 = make_top_value_set();
      auto op2 = make_interval(val1, val2, environment, ns);
      auto result = add(op1, op2, environment, ns);

      THEN("= TOP")
      {
        EXPECT_TOP(result);
      }
    }
  }
  GIVEN("adding an interval and a constant")
  {
    WHEN("[2,2] + 1")
    {
      auto op1 = make_interval(val2, val2, environment, ns);
      auto op2 = make_constant(val1, environment, ns);
      auto result = add_as_interval(op1, op2, environment, ns);

      THEN("= [3,3]")
      {
        EXPECT(result, val3, val3);
      }
    }
    WHEN("[2,4] + 1")
    {
      auto op1 = make_interval(val2, val4, environment, ns);
      auto op2 = make_constant(val1, environment, ns);
      auto result = add_as_interval(op1, op2, environment, ns);

      THEN("= [3,5]")
      {
        EXPECT(result, val3, val5);
      }
    }
  }
  GIVEN("adding an interval and a value-set of constants")
  {
    WHEN("[2,2] + { 1 }")
    {
      auto op1 = make_interval(val2, val2, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= {[3,3]}")
      {
        EXPECT(result, {constant_interval_exprt(val3, val3)});
      }
    }
    WHEN("[2,4] + { 1 }")
    {
      auto op1 = make_interval(val2, val4, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= {[3,5]}")
      {
        EXPECT(result, {constant_interval_exprt(val3, val5)});
      }
    }
    WHEN("[1,2] + { 1, 2, 3 }")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_value_set({val1, val2, val3}, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= {[2,3], [3,4], [4,5]}")
      {
        EXPECT(
          result,
          {constant_interval_exprt(val2, val3),
           constant_interval_exprt(val3, val4),
           constant_interval_exprt(val4, val5)});
      }
    }
  }

  GIVEN("adding two value_sets")
  {
    WHEN("{ 1 } + { 1 }")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { 2 }")
      {
        EXPECT(result, {val2});
      }
    }
    WHEN("{ 1, 2 } + { 1 }")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { 2, 3 }")
      {
        EXPECT(result, {val2, val3});
      }
    }
    WHEN("{ 1 } + { 1, 2 }")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { 2, 3 }")
      {
        EXPECT(result, {val2, val3});
      }
    }
    WHEN("{ 1 } + { 1, 2 }")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { 2, 3 }")
      {
        EXPECT(result, {val2, val3});
      }
    }
    WHEN("{ 1, 2 } + { 1, 2, 3 }")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set({val1, val2, val3}, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { 2, 3, 4, 5 }")
      {
        EXPECT(result, {val2, val3, val4, val5});
      }
    }
  }
  GIVEN("adding a value set and a constant")
  {
    WHEN("{ 2 } + 1")
    {
      auto op1 = make_value_set(val2, environment, ns);
      auto op2 = make_constant(val1, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { 3 }")
      {
        EXPECT(result, {val3});
      }
    }
    WHEN("{ 2, 3, 4 } + 1")
    {
      auto op1 = make_value_set({val2, val3, val4}, environment, ns);
      auto op2 = make_constant(val1, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { 3, 4, 5 }")
      {
        EXPECT(result, {val3, val4, val5});
      }
    }
  }
  GIVEN("adding a value-set of constants and an interval")
  {
    WHEN("{ 1 } + [2,2]")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_interval(val2, val2, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= {[3,3]}")
      {
        EXPECT(result, {constant_interval_exprt(val3, val3)});
      }
    }
    WHEN("{ 1 } + [2,4]")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_interval(val2, val4, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= {[3,5]}")
      {
        EXPECT(result, {constant_interval_exprt(val3, val5)});
      }
    }
    WHEN("{ 1, 2, 3 } + [1,2]")
    {
      auto op1 = make_value_set({val1, val2, val3}, environment, ns);
      auto op2 = make_interval(val1, val2, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= {[2,3], [3,4], [4,5]}")
      {
        EXPECT(
          result,
          {constant_interval_exprt(val2, val3),
           constant_interval_exprt(val3, val4),
           constant_interval_exprt(val4, val5)});
      }
    }
  }
  GIVEN("adding a value-set of intervals and constants with a constant")
  {
    auto interval12 = constant_interval_exprt(val1, val2);
    auto interval23 = constant_interval_exprt(val2, val3);
    auto interval34 = constant_interval_exprt(val3, val4);
    auto interval45 = constant_interval_exprt(val4, val5);

    WHEN("{ [1,2] } + 2")
    {
      auto op1 = make_value_set(interval12, environment, ns);
      auto op2 = make_constant(val2, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { [3,4] }")
      {
        EXPECT(result, {interval34});
      }
    }
    WHEN("{ [1,2], 3 } + 2")
    {
      auto op1 = make_value_set({interval12, val3}, environment, ns);
      auto op2 = make_constant(val2, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { [3,4], 5 }")
      {
        EXPECT(result, {interval34, val5});
      }
    }
    WHEN("{ [1,2], [2,3] } + 2")
    {
      auto op1 = make_value_set({interval12, interval23}, environment, ns);
      auto op2 = make_constant(val2, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { [3,4], [4,5] }")
      {
        EXPECT(result, {interval34, interval45});
      }
    }
  }
  GIVEN("adding a value-set of intervals and constants with an interval")
  {
    auto interval12 = constant_interval_exprt(val1, val2);
    auto interval23 = constant_interval_exprt(val2, val3);
    auto interval34 = constant_interval_exprt(val3, val4);
    auto interval45 = constant_interval_exprt(val4, val5);
    auto interval24 = constant_interval_exprt(val2, val4);
    auto interval35 = constant_interval_exprt(val3, val5);

    WHEN("{ [1,2] } + [1,2]")
    {
      auto op1 = make_value_set(interval12, environment, ns);
      auto op2 = make_interval(interval12, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { [2,4] }")
      {
        EXPECT(result, {interval24});
      }
    }
    WHEN("{ [1,2], 1 } + [1,2]")
    {
      auto op1 = make_value_set({interval12, val1}, environment, ns);
      auto op2 = make_interval(interval12, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { [2,4], [2,3] }")
      {
        EXPECT(result, {interval24, interval23});
      }
    }
    WHEN("{ [1,2], [2,3] } + [1,2]")
    {
      auto op1 = make_value_set({interval12, interval23}, environment, ns);
      auto op2 = make_interval(interval12, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { [2,4], [3,5] }")
      {
        EXPECT(result, {interval24, interval35});
      }
    }
  }
  GIVEN("adding a value-set of intervals and constants with a value-set")
  {
    auto interval12 = constant_interval_exprt(val1, val2);
    auto interval23 = constant_interval_exprt(val2, val3);
    auto interval34 = constant_interval_exprt(val3, val4);
    auto interval45 = constant_interval_exprt(val4, val5);
    auto interval24 = constant_interval_exprt(val2, val4);
    auto interval35 = constant_interval_exprt(val3, val5);

    WHEN("{ [1,2] } + { 1, 2 }")
    {
      auto op1 = make_value_set(interval12, environment, ns);
      auto op2 = make_value_set({val1, val2}, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { [2,3], [3,4] }")
      {
        EXPECT(result, {interval23, interval34});
      }
    }
    WHEN("{ [1,2] } + { [1,2] }")
    {
      auto op1 = make_value_set(interval12, environment, ns);
      auto op2 = make_value_set(interval12, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { [2,4] }")
      {
        EXPECT(result, {interval24});
      }
    }
    WHEN("{ [1,2], 1 } + { [1,2] }")
    {
      auto op1 = make_value_set({interval12, val1}, environment, ns);
      auto op2 = make_value_set(interval12, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { [2,4], [2,3] }")
      {
        EXPECT(result, {interval24, interval23});
      }
    }
    WHEN("{ [1,2], [2,3] } + { [1,2] }")
    {
      auto op1 = make_value_set({interval12, interval23}, environment, ns);
      auto op2 = make_interval(interval12, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { [2,4], [3,5] }")
      {
        EXPECT(result, {interval24, interval35});
      }
    }
    WHEN("{ [1,2], 1 } + { [1,2], 1 }")
    {
      auto op1 = make_value_set({interval12, val1}, environment, ns);
      auto op2 = make_value_set({interval12, val1}, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { [2,4], [2,3], 2 }")
      {
        EXPECT(result, {interval24, interval23, val2});
      }
    }
  }
  GIVEN("multiple operands")
  {
    WHEN("{ 1, 2, 3 } + 1 + 1")
    {
      auto op1 = make_value_set({val1, val2, val3}, environment, ns);
      auto op2 = make_constant(val1, environment, ns);
      auto op3 = make_constant(val1, environment, ns);

      auto result = add_as_value_set(op1, op2, op3, environment, ns);

      THEN("= { 3, 4, 5 }")
      {
        EXPECT(result, {val3, val4, val5});
      }
    }
    WHEN("{ 1, 2, 3 } + { 1 } + 1")
    {
      auto op1 = make_value_set({val1, val2, val3}, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);
      auto op3 = make_constant(val1, environment, ns);

      auto result = add_as_value_set(op1, op2, op3, environment, ns);

      THEN("= { 3, 4, 5 }")
      {
        EXPECT(result, {val3, val4, val5});
      }
    }
  }
  GIVEN("adding a value_set and TOP")
  {
    WHEN("{ 1, 2 } + TOP constant")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_top_constant();

      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("the result is top")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("{ 1, 2 } + TOP interval")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_top_interval();

      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("the result is top")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("{ 1, 2 } + TOP value_set")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_top_value_set();

      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("the result is top")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("TOP constant + { 1, 2 }")
    {
      auto op1 = make_top_constant();
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("the result is top")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("TOP interval + { 1, 2 }")
    {
      auto op1 = make_top_interval();
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("the result is top")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("TOP value_set + { 1, 2 }")
    {
      auto op1 = make_top_value_set();
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("the result is top")
      {
        EXPECT_TOP(result);
      }
    }
  }
}
