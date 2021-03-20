/*******************************************************************\

 Module: Unit tests for constant_abstract_valuet::merge

 Author: DiffBlue Limited.

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <testing-utils/use_catch.h>

#include <util/bitvector_types.h>

static merge_result<const constant_abstract_valuet>
merge(abstract_object_pointert op1, abstract_object_pointert op2)
{
  bool modified;
  auto result = abstract_objectt::merge(op1, op2, modified);

  return {modified, as_constant(result)};
}

SCENARIO(
  "merge constant_abstract_value",
  "[core][analyses][variable-sensitivity][constant_abstract_value][merge]")
{
  const typet type = signedbv_typet(32);
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

  GIVEN("merging two constants")
  {
    WHEN("merging 1 with 1")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto merged = merge(op1, op2);

      THEN("the result 1 is unchanged")
      {
        EXPECT_UNMODIFIED(merged, val1);
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
      auto top2 = make_top_constant();

      auto merged = merge(op1, top2);

      THEN("result should be TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging 1 with BOTTOM")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto bottom2 = make_bottom_constant();

      auto merged = merge(op1, bottom2);

      THEN("the result 1 is unchanged")
      {
        EXPECT_UNMODIFIED(merged, val1);
      }
    }
    WHEN("merging TOP with 1")
    {
      auto top1 = make_top_constant();
      auto op2 = make_constant(val1, environment, ns);

      auto merged = merge(top1, op2);

      THEN("result should be TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging TOP with TOP")
    {
      auto top1 = make_top_constant();
      auto top2 = make_top_constant();

      auto merged = merge(top1, top2);

      THEN("result should be TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging TOP with BOTTOM")
    {
      auto top1 = make_top_constant();
      auto bottom2 = make_bottom_constant();

      auto merged = merge(top1, bottom2);

      THEN("result should be TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging BOTTOM with 1")
    {
      auto bottom1 = make_bottom_constant();
      auto op2 = make_constant(val1, environment, ns);

      auto merged = merge(bottom1, op2);

      THEN("the result is 1")
      {
        EXPECT_MODIFIED(merged, val1);
      }
    }
    WHEN("merging BOTTOM with TOP")
    {
      auto bottom1 = make_bottom_constant();
      auto top2 = make_top_constant();

      auto merged = merge(bottom1, top2);

      THEN("result should be TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging BOTTOM with BOTTOM")
    {
      auto bottom1 = make_bottom_constant();
      auto bottom2 = make_bottom_constant();

      auto merged = merge(bottom1, bottom2);

      THEN("result is BOTTOM")
      {
        CHECK_FALSE(merged.modified);
        EXPECT_BOTTOM(merged.result);
      }
    }
  }
}

SCENARIO(
  "merge constant_abstract_value with an abstract object",
  "[core][analyses][variable-sensitivity][constant_abstract_value][merge]")
{
  const typet type = signedbv_typet(32);
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

  GIVEN("merging a constant and an abstract object")
  {
    WHEN("merging 1 with TOP")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto top2 = make_top_object();

      auto merged = merge(op1, top2);

      THEN("result is TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging 1 with BOTTOM")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto bottom2 = make_bottom_object();

      auto merged = merge(op1, bottom2);

      THEN("the result 1 is unchanged")
      {
        EXPECT_UNMODIFIED(merged, val1);
      }
    }
    WHEN("merging TOP constant with TOP")
    {
      auto top1 = make_top_constant();
      auto top2 = make_top_object();

      auto merged = merge(top1, top2);

      THEN("result is TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging TOP constant with BOTTOM")
    {
      auto top1 = make_top_constant();
      auto bottom2 = make_bottom_object();

      auto merged = merge(top1, bottom2);

      THEN("result is TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging BOTTOM constant with TOP")
    {
      auto bottom1 = make_bottom_constant();
      auto top2 = make_top_object();

      auto merged = merge(bottom1, top2);

      THEN("result is TOP")
      {
        EXPECT_TOP(merged.result);
      }
    }
    WHEN("merging BOTTOM constant with BOTTOM")
    {
      auto bottom1 = make_bottom_constant();
      auto top2 = make_bottom_object();

      auto merged = merge(bottom1, top2);

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
  const typet type = signedbv_typet(32);
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

  GIVEN("an abstract object and a constant")
  {
    WHEN("merging TOP with 1")
    {
      auto top1 = make_top_object();
      auto op2 = make_constant(val1, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(top1, op2, modified);

      THEN("the result is TOP")
      {
        EXPECT_UNMODIFIED(result, modified);
        EXPECT_TOP(result);
      }
    }
    WHEN("merging TOP with TOP constant")
    {
      auto top1 = make_top_object();
      auto top2 = make_top_constant();

      bool modified;
      auto result = abstract_objectt::merge(top1, top2, modified);

      THEN("the result is TOP")
      {
        EXPECT_UNMODIFIED(result, modified);
        EXPECT_TOP(result);
      }
    }
    WHEN("merging TOP with BOTTOM constant")
    {
      auto top1 = make_top_object();
      auto bottom2 = make_bottom_constant();

      bool modified;
      auto result = abstract_objectt::merge(top1, bottom2, modified);

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
    WHEN("merging BOTTOM with TOP constant")
    {
      auto op1 = make_bottom_object();
      auto top2 = make_top_constant();

      bool modified;
      auto result = abstract_objectt::merge(op1, top2, modified);

      THEN("the result is TOP")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("merging BOTTOM with BOTTOM constant")
    {
      auto bottom1 = make_bottom_object();
      auto bottom2 = make_bottom_constant();

      bool modified;
      auto result = abstract_objectt::merge(bottom1, bottom2, modified);

      THEN("The original AO should be returned")
      {
        EXPECT_UNMODIFIED(result, modified);
        EXPECT_BOTTOM(result);
      }
    }
  }
}
