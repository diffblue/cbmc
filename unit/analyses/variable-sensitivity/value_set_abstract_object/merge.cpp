/*******************************************************************\

 Module: Unit tests for value_set_abstract_valuet::merge

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include "value_set_test_helpers.h"
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <testing-utils/use_catch.h>
#include <util/arith_tools.h>
#include <util/mathematical_types.h>

SCENARIO(
  "merging two value_set_abstract_objects",
  "[core][analyses][variable-sensitivity][value_set_abstract_object][merge]")
{
  GIVEN("Two value sets")
  {
    const exprt val1 = from_integer(1, integer_typet());
    const exprt val2 = from_integer(2, integer_typet());
    const exprt val3 = from_integer(3, integer_typet());
    const exprt val4 = from_integer(4, integer_typet());

    auto object_factory = variable_sensitivity_object_factoryt::configured_with(
      vsd_configt::value_set());
    auto environment = abstract_environmentt{object_factory};
    environment.make_top();
    auto symbol_table = symbol_tablet{};
    auto ns = namespacet{symbol_table};

    WHEN("merging { 1 } with { 1 }")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result { 1 } is unchanged ")
      {
        EXPECT_UNMODIFIED(value_set_result, modified, {val1});
      }
    }

    WHEN("merging { 1 } with { 2 }")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_value_set(val2, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is { 1, 2 }")
      {
        EXPECT(value_set_result, {val1, val2});
      }
    }

    WHEN("merging { 1, 2 } with { 2 }")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set(val2, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result { 1, 2 } is unchanged")
      {
        EXPECT_UNMODIFIED(value_set_result, modified, {val1, val2});
      }
    }

    WHEN("merging { 1, 2 } with { 3, 4 }")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set({val3, val4}, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is { 1, 2, 3, 4 }")
      {
        EXPECT(value_set_result, {val1, val2, val3, val4});
      }
    }

    WHEN("merging { 1, 2, 3 } with { 1, 3, 4 }")
    {
      auto op1 = make_value_set({val1, val2, val3}, environment, ns);
      auto op2 = make_value_set({val1, val3, val4}, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is { 1, 2, 3, 4 }")
      {
        EXPECT(value_set_result, {val1, val2, val3, val4});
      }
    }
  }
}

SCENARIO(
  "merging a value_set with a constant",
  "[core][analyses][variable-sensitivity][value_set_abstract_object][merge]")
{
  GIVEN("A value set and a constant")
  {
    const exprt val1 = from_integer(1, integer_typet());
    const exprt val2 = from_integer(2, integer_typet());
    const exprt val3 = from_integer(3, integer_typet());
    const exprt val4 = from_integer(4, integer_typet());

    auto object_factory = variable_sensitivity_object_factoryt::configured_with(
      vsd_configt::value_set());
    auto environment = abstract_environmentt{object_factory};
    environment.make_top();
    auto symbol_table = symbol_tablet{};
    auto ns = namespacet{symbol_table};

    WHEN("merging { 1 } with 1")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result { 1 } is unchanged ")
      {
        EXPECT_UNMODIFIED(value_set_result, modified, {val1});
      }
    }

    WHEN("merging { 1 } with 2")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_constant(val2, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is { 1, 2 }")
      {
        EXPECT(value_set_result, {val1, val2});
      }
    }

    WHEN("merging { 1, 2 } with 2")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_constant(val2, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result { 1, 2 } is unchanged")
      {
        EXPECT_UNMODIFIED(value_set_result, modified, {val1, val2});
      }
    }
  }
}

SCENARIO(
  "merging a value_set with a TOP value",
  "[core][analyses][variable-sensitivity][value_set_abstract_object][merge]")
{
  GIVEN("A value set and a TOP constant")
  {
    const exprt val1 = from_integer(1, integer_typet());
    const exprt val2 = from_integer(2, integer_typet());

    auto object_factory = variable_sensitivity_object_factoryt::configured_with(
      vsd_configt::value_set());
    auto environment = abstract_environmentt{object_factory};
    environment.make_top();
    auto symbol_table = symbol_tablet{};
    auto ns = namespacet{symbol_table};

    WHEN("merging { 1, 2 } with TOP constant")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = std::make_shared<constant_abstract_valuet>(val1.type());
      REQUIRE(op2->is_top());

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is top")
      {
        EXPECT_TOP(value_set_result);
      }
    }

    WHEN("merging { 1, 2 } with TOP interval")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 =
        std::make_shared<interval_abstract_valuet>(unsignedbv_typet(32));
      REQUIRE(op2->is_top());

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is top")
      {
        EXPECT_TOP(value_set_result);
      }
    }

    WHEN("merging { 1, 2 } with TOP value-set")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = std::make_shared<value_set_abstract_objectt>(val1.type());
      REQUIRE(op2->is_top());

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is top")
      {
        EXPECT_TOP(value_set_result);
      }
    }
  }
}
