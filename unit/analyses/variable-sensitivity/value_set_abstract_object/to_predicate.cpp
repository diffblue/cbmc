/*******************************************************************\

 Module: Tests for value_set_abstract_objectt::to_predicate

 Author: Jez Higgins

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/symbol_table.h>

SCENARIO(
  "value_set_abstract_object to predicate",
  "[core][analyses][variable-sensitivity][value_set_abstract_object][to_"
  "predicate]")
{
  const typet type = signedbv_typet(32);
  const exprt val0 = from_integer(0, type);
  const exprt val1 = from_integer(1, type);
  const exprt val2 = from_integer(2, type);
  const exprt val3 = from_integer(3, type);
  const exprt interval_0_1 = constant_interval_exprt(val0, val1);
  const exprt interval_1_2 = constant_interval_exprt(val1, val2);
  const exprt interval_0_2 = constant_interval_exprt(val1, val2);
  const exprt interval_2_3 = constant_interval_exprt(val2, val3);

  const exprt x_name = symbol_exprt(dstringt("x"), type);

  auto config = vsd_configt::constant_domain();
  config.context_tracking.data_dependency_context = false;
  config.context_tracking.last_write_context = false;
  auto object_factory =
    variable_sensitivity_object_factoryt::configured_with(config);
  abstract_environmentt environment{object_factory};
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("value_set_abstract_object")
  {
    WHEN("it is TOP")
    {
      auto obj = make_top_value_set();
      THEN_PREDICATE(obj, "TRUE");
    }
    WHEN("it is BOTTOM")
    {
      auto obj = make_bottom_value_set();
      THEN_PREDICATE(obj, "FALSE");
    }
    WHEN("{ 2 }")
    {
      auto obj = make_value_set(val2, environment, ns);
      THEN_PREDICATE(obj, "x == 2");
    }
    WHEN("{ [2, 2] }")
    {
      auto obj =
        make_value_set(constant_interval_exprt(val2, val2), environment, ns);
      THEN_PREDICATE(obj, "x == 2");
    }
    WHEN("{ 0, 2 }")
    {
      auto obj = make_value_set({val0, val2}, environment, ns);
      THEN_PREDICATE(obj, "x == 0 || x == 2");
    }
    WHEN("{ 0, 1, 2 }")
    {
      auto obj = make_value_set({val0, val1, val2}, environment, ns);
      THEN_PREDICATE(obj, "x == 0 || x == 1 || x == 2");
    }
    WHEN("{ [0, 1] }")
    {
      auto obj = make_value_set(interval_0_1, environment, ns);
      THEN_PREDICATE(obj, "0 <= x && x <= 1");
    }
    WHEN("{ [0, 1], 2 }")
    {
      auto obj = make_value_set({interval_0_1, val2}, environment, ns);
      THEN_PREDICATE(obj, "x == 2 || 0 <= x && x <= 1");
    }
    WHEN("{ [0, 1], 2, 3 }")
    {
      auto obj = make_value_set({interval_0_1, val2, val3}, environment, ns);
      THEN_PREDICATE(obj, "x == 2 || x == 3 || 0 <= x && x <= 1");
    }
    WHEN("{ [0, 1], 1, 2 }")
    {
      auto obj = make_value_set({interval_0_1, val1, val2}, environment, ns);
      THEN_PREDICATE(obj, "x == 2 || 0 <= x && x <= 1");
    }
    WHEN("{ [0, 1], [1, 2] }")
    {
      auto obj = make_value_set({interval_0_1, interval_1_2}, environment, ns);
      THEN_PREDICATE(obj, "0 <= x && x <= 2");
    }
    WHEN("{ [0, 2], [1, 2] }")
    {
      auto obj = make_value_set({interval_0_1, interval_1_2}, environment, ns);
      THEN_PREDICATE(obj, "0 <= x && x <= 2");
    }
    WHEN("{ [0, 1], [2, 3] }")
    {
      auto obj = make_value_set({interval_0_1, interval_2_3}, environment, ns);
      THEN_PREDICATE(obj, "0 <= x && x <= 1 || 2 <= x && x <= 3");
    }
  }
}
