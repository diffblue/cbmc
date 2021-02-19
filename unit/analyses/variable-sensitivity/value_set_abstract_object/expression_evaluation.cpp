/*******************************************************************\

 Module: Unit tests for value_set_abstract_valuet::expression_transform

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include "../variable_sensitivity_test_helpers.h"
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <testing-utils/use_catch.h>
#include <util/arith_tools.h>
#include <util/mathematical_types.h>

SCENARIO(
  "value_set expression evaluation",
  "[core][analyses][variable-sensitivity][value_set_abstract_object]["
  "expression_transform]")
{
  const exprt val1 = from_integer(1, integer_typet());
  const exprt val2 = from_integer(2, integer_typet());
  const exprt val3 = from_integer(3, integer_typet());
  const exprt val4 = from_integer(4, integer_typet());
  const exprt val5 = from_integer(5, integer_typet());

  auto config = vsd_configt::value_set();
  config.context_tracking.data_dependency_context = false;
  config.context_tracking.last_write_context = false;
  auto object_factory =
    variable_sensitivity_object_factoryt::configured_with(config);
  auto environment = abstract_environmentt{object_factory};
  environment.make_top();
  auto symbol_table = symbol_tablet{};
  auto ns = namespacet{symbol_table};

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
    WHEN("{ 1 } + 1")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_constant(val1, environment, ns);
      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("= { 2 }")
      {
        EXPECT(result, {val2});
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
      auto op2 = std::make_shared<constant_abstract_valuet>(val1.type());
      REQUIRE(op2->is_top());

      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("the result is top")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("{ 1, 2 } + TOP value_set")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = std::make_shared<value_set_abstract_objectt>(val1.type());
      REQUIRE(op2->is_top());

      auto result = add_as_value_set(op1, op2, environment, ns);

      THEN("the result is top")
      {
        EXPECT_TOP(result);
      }
    }
  }
}
