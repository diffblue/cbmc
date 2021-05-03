/*******************************************************************\

 Module: Unit tests for value_set_abstract_objectt::merge

 Author: Jez Higgins.

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>

static merge_result<const value_set_abstract_objectt>
widening_merge(abstract_object_pointert op1, abstract_object_pointert op2)
{
  auto result = abstract_objectt::merge(op1, op2, widen_modet::could_widen);

  return {result.modified, as_value_set(result.object)};
}

SCENARIO(
  "widening merge value_set_abstract_object",
  "[core][analyses][variable-sensitivity][value_set_abstract_object][merge]")
{
  auto type = signedbv_typet(32);
  auto val0 = from_integer(0, type);
  auto val1 = from_integer(1, type);
  auto val2 = from_integer(2, type);
  auto val3 = from_integer(3, type);
  auto val4 = from_integer(4, type);
  auto val5 = from_integer(5, type);
  auto val6 = from_integer(6, type);
  auto val7 = from_integer(7, type);
  auto val8 = from_integer(8, type);
  auto val9 = from_integer(9, type);
  auto val10 = from_integer(10, type);
  auto val11 = from_integer(11, type);
  auto val12 = from_integer(12, type);
  auto val13 = from_integer(13, type);

  auto config = vsd_configt::constant_domain();
  config.context_tracking.data_dependency_context = false;
  config.context_tracking.last_write_context = false;
  auto object_factory =
    variable_sensitivity_object_factoryt::configured_with(config);
  abstract_environmentt environment{object_factory};
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("value_set merges which don't widen")
  {
    WHEN("merging {1, 2} with {1, 2}")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is unmodified {1, 2}")
      {
        EXPECT_UNMODIFIED(merged, {val1, val2});
      }
    }
    WHEN("merging {1, 5} with {2, 3}")
    {
      auto op1 = make_value_set({val1, val5}, environment, ns);
      auto op2 = make_value_set({val2, val3}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is unmodified {1, 2, 3, 5}")
      {
        EXPECT_MODIFIED(merged, {val1, val2, val3, val5});
      }
    }
    WHEN("merging { 1, 4, 7, 10, 13 } with { 2, 3, 5, 6, 8, 9, 11, 12 }")
    {
      auto op1 =
        make_value_set({val1, val4, val7, val10, val13}, environment, ns);
      auto op2 = make_value_set(
        {val2, val3, val5, val6, val8, val9, val11, val12}, environment, ns);

      auto merged = widening_merge(op1, op2);

      THEN("result is compacted but not widened { [1, 5], 6, 7, 8, [9, 13]")
      {
        auto interval_1_5 = constant_interval_exprt(val1, val5);
        auto interval_9_13 = constant_interval_exprt(val9, val13);
        EXPECT_MODIFIED(
          merged, {interval_1_5, val6, val7, val8, interval_9_13});
      }
    }
  }
}
