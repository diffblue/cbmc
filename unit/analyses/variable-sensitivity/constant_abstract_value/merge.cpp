/*******************************************************************\

 Module: Unit tests for constant_abstract_valuet::merge

 Author: DiffBlue Limited.

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <testing-utils/use_catch.h>
#include <typeinfo>
#include <util/arith_tools.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

struct constant_merge_result
{
  bool modified;
  std::shared_ptr<const constant_abstract_valuet> result;
};

static constant_merge_result merge(
  std::shared_ptr<const abstract_objectt> op1,
  std::shared_ptr<const abstract_objectt> op2)
{
  bool modified;
  auto result = abstract_objectt::merge(op1, op2, modified);

  return {modified, as_constant(result)};
}

static abstract_object_pointert make_bottom_object()
{
  return std::make_shared<abstract_objectt>(integer_typet(), false, true);
}

static abstract_object_pointert make_top_object()
{
  return std::make_shared<abstract_objectt>(integer_typet(), true, false);
}

SCENARIO(
  "merge_constant_abstract_value",
  "[core][analyses][variable-sensitivity][constant_abstract_value][merge]")
{
  const exprt val1 = from_integer(1, integer_typet());
  const exprt val2 = from_integer(2, integer_typet());

  auto object_factory = variable_sensitivity_object_factoryt::configured_with(
    vsd_configt::constant_domain());
  abstract_environmentt environment{object_factory};
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("merging two constants")
  {
    WHEN("merging 1 with 1")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto merged = merge(op1, op2);

      THEN("the result 1 is unchanged")
      {
        EXPECT_UNMODIFIED(merged.result, merged.modified, val1);
      }
    }
    WHEN("merging 1 with 2")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_constant(val2, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result should be TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging 1 with TOP")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_constant(val1, true);

      auto merged = merge(op1, op2);

      THEN("result should be TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging 1 with BOTTOM")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_constant(val1, false);

      auto merged = merge(op1, op2);

      THEN("the result 1 is unchanged")
      {
        EXPECT_UNMODIFIED(merged.result, merged.modified, val1);
      }
    }
    WHEN("merging TOP with 1")
    {
      auto op1 = make_constant(val1, true);
      auto op2 = make_constant(val1, environment, ns);

      auto merged = merge(op1, op2);

      THEN("result should be TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging TOP with TOP")
    {
      auto op1 = make_constant(val1, true);
      auto op2 = make_constant(val1, true);

      auto merged = merge(op1, op2);

      THEN("result should be TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging TOP with BOTTOM")
    {
      auto op1 = make_constant(val1, true);
      auto op2 = make_constant(val1, false);

      auto merged = merge(op1, op2);

      THEN("result should be TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging BOTTOM with 1")
    {
      auto op1 = make_constant(val1, false);
      auto op2 = make_constant(val1, environment, ns);

      auto merged = merge(op1, op2);

      THEN("the result is 1")
      {
        EXPECT(merged.result, val1);
      }
    }
    WHEN("merging BOTTOM with TOP")
    {
      auto op1 = make_constant(val1, false);
      auto op2 = make_constant(val1, true);

      auto merged = merge(op1, op2);

      THEN("result should be TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging BOTTOM with BOTTOM")
    {
      auto op1 = make_constant(val1, false);
      auto op2 = make_constant(val1, false);

      auto merged = merge(op1, op2);

      THEN("result is BOTTOM")
      {
        EXPECT_BOTTOM(merged.result);
      }
    }
  }
}

SCENARIO(
  "merging a constant with an abstract object",
  "[core][analyses][variable-sensitivity][constant_abstract_value][merge]")
{
  const exprt val1 = from_integer(1, integer_typet());
  const exprt val2 = from_integer(2, integer_typet());

  auto object_factory = variable_sensitivity_object_factoryt::configured_with(
    vsd_configt::constant_domain());
  abstract_environmentt environment{object_factory};
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("merging a constant and an abstract object")
  {
    WHEN("merging 1 with TOP")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_top_object();

      auto merged = merge(op1, op2);

      THEN("result is TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging 1 with BOTTOM")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_bottom_object();

      auto merged = merge(op1, op2);

      THEN("the result 1 is unchanged")
      {
        EXPECT_UNMODIFIED(merged.result, merged.modified, val1);
      }
    }
    WHEN("merging constant TOP with TOP")
    {
      auto op1 = make_constant(val1, true);
      auto op2 = make_top_object();

      auto merged = merge(op1, op2);

      THEN("result is TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging constant TOP with BOTTOM")
    {
      auto op1 = make_constant(val1, true);
      auto op2 = make_bottom_object();

      auto merged = merge(op1, op2);

      THEN("result is TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging constant BOTTOM with TOP")
    {
      auto op1 = make_constant(val1, false);
      auto op2 = make_top_object();

      auto merged = merge(op1, op2);

      THEN("result is TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging constant BOTTOM with BOTTOM")
    {
      auto op1 = make_constant(val1, false);
      auto op2 = make_bottom_object();

      auto merged = merge(op1, op2);

      THEN("result is TOP")
      {
        EXPECT_BOTTOM(merged.result);
      }
    }
  }
}

SCENARIO(
  "merging an abstract object with a constant",
  "[core][analyses][variable-sensitivity][constant_abstract_value][merge]")
{
  const exprt val1 = from_integer(1, integer_typet());
  const exprt val2 = from_integer(2, integer_typet());

  auto object_factory = variable_sensitivity_object_factoryt::configured_with(
    vsd_configt::constant_domain());
  abstract_environmentt environment{object_factory};
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("an abstract object and a constant")
  {
    WHEN("merging TOP with 1")
    {
      auto op1 = make_top_object();
      auto op2 = make_constant(val1, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      THEN("the result is TOP")
      {
        EXPECT_UNMODIFIED(result, modified);
        EXPECT_TOP(result);
      }
    }
    WHEN("merging TOP with constant TOP")
    {
      auto op1 = make_top_object();
      auto op2 = make_constant(val1, true);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      THEN("the result is TOP")
      {
        EXPECT_UNMODIFIED(result, modified);
        EXPECT_TOP(result);
      }
    }
    WHEN("merging TOP with constant BOTTOM")
    {
      auto op1 = make_top_object();
      auto op2 = make_constant(val1, false);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      THEN("the result is TOP")
      {
        EXPECT_UNMODIFIED(result, modified);
        EXPECT_TOP(result);
      }
    }
    WHEN("merging BOTTOM with 1")
    {
      auto op1 = make_bottom_object();
      auto op2 = make_constant(val1, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      THEN("the result is TOP")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("merging BOTTOM with constant TOP")
    {
      auto op1 = make_bottom_object();
      auto op2 = make_constant(val1, true);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      THEN("the result is TOP")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("merging BOTTOM with constant BOTTOM")
    {
      auto op1 = make_bottom_object();
      auto op2 = make_constant(val1, false);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      THEN("The original AO should be returned")
      {
        EXPECT_UNMODIFIED(result, modified);
        EXPECT_BOTTOM(result);
      }
    }
  }
}
