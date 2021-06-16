/*******************************************************************\

 Module: Unit tests for variable/sensitivity/abstract_object::merge

 Author: DiffBlue Limited.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <analyses/variable-sensitivity/abstract_object.h>

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>

SCENARIO(
  "merge abstract object",
  "[core][analyses][variable-sensitivity][abstract_object][merge]")
{
  GIVEN("merging two abstract objects")
  {
    WHEN("merging TOP with TOP")
    {
      abstract_object_pointert op1 = make_top_object();
      abstract_object_pointert op2 = make_top_object();

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED(result);
        EXPECT_TOP(result);
      }
    }
    WHEN("merging TOP with BOTTOM")
    {
      abstract_object_pointert op1 = make_top_object();
      abstract_object_pointert op2 = make_bottom_object();

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      THEN("result is unmodified TOP")
      {
        EXPECT_UNMODIFIED(result);
        EXPECT_TOP(result);
      }
    }
    WHEN("merging BOTTOM with TOP")
    {
      abstract_object_pointert op1 = make_bottom_object();
      abstract_object_pointert op2 = make_top_object();

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      THEN("result is modified TOP")
      {
        EXPECT_MODIFIED(result);
        EXPECT_TOP(result);
      }
    }
    WHEN("merging BOTTOM with BOTTOM")
    {
      abstract_object_pointert op1 = make_bottom_object();
      abstract_object_pointert op2 = make_bottom_object();

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      THEN("result is unmodified BOTTOM")
      {
        EXPECT_UNMODIFIED(result);
        EXPECT_BOTTOM(result);
      }
    }
  }

  GIVEN("an abstract object and a constant")
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

    WHEN("merging TOP with 1")
    {
      auto top1 = make_top_object();
      auto op2 = make_constant(val1, environment, ns);

      auto result = abstract_objectt::merge(top1, op2, widen_modet::no);

      THEN("the result is unmodified TOP")
      {
        EXPECT_UNMODIFIED(result);
        EXPECT_TOP(result);
      }
    }
    WHEN("merging TOP with TOP constant")
    {
      auto top1 = make_top_object();
      auto top2 = make_top_constant();

      auto result = abstract_objectt::merge(top1, top2, widen_modet::no);

      THEN("the result is unmodified TOP")
      {
        EXPECT_UNMODIFIED(result);
        EXPECT_TOP(result);
      }
    }
    WHEN("merging TOP with BOTTOM constant")
    {
      auto top1 = make_top_object();
      auto bottom2 = make_bottom_constant();

      auto result = abstract_objectt::merge(top1, bottom2, widen_modet::no);

      THEN("the result is unmodified TOP")
      {
        EXPECT_UNMODIFIED(result);
        EXPECT_TOP(result);
      }
    }
    WHEN("merging BOTTOM with 1")
    {
      auto op1 = make_bottom_object();
      auto op2 = make_constant(val1, environment, ns);

      auto result = abstract_objectt::merge(op1, op2, widen_modet::no);

      THEN("the result is modified TOP")
      {
        EXPECT_MODIFIED(result);
        EXPECT_TOP(result);
      }
    }
    WHEN("merging BOTTOM with TOP constant")
    {
      auto op1 = make_bottom_object();
      auto top2 = make_top_constant();

      auto result = abstract_objectt::merge(op1, top2, widen_modet::no);

      THEN("the result is modified TOP")
      {
        EXPECT_MODIFIED(result);
        EXPECT_TOP(result);
      }
    }
    WHEN("merging BOTTOM with BOTTOM constant")
    {
      auto bottom1 = make_bottom_object();
      auto bottom2 = make_bottom_constant();

      auto result = abstract_objectt::merge(bottom1, bottom2, widen_modet::no);

      THEN("result is unmodified BOTTOM")
      {
        EXPECT_UNMODIFIED(result);
        EXPECT_BOTTOM(result);
      }
    }
  }
}
