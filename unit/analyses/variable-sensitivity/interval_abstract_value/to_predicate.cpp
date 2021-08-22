/*******************************************************************\

 Module: Tests for interval_abstract_valuet::to_predicate

 Author: Jez Higgins

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/symbol_table.h>

SCENARIO(
  "interval_abstract_value to predicate",
  "[core][analyses][variable-sensitivity][interval_abstract_value][to_"
  "predicate]")
{
  const typet type = signedbv_typet(32);
  const exprt val0 = from_integer(0, type);
  const exprt val1 = from_integer(1, type);
  const exprt val2 = from_integer(2, type);

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

  GIVEN("interval_abstract_value")
  {
    WHEN("it is TOP")
    {
      auto obj = make_top_interval();
      THEN_PREDICATE(obj, "TRUE");
    }
    WHEN("it is BOTTOM")
    {
      auto obj = make_bottom_interval();
      THEN_PREDICATE(obj, "FALSE");
    }
    WHEN("[ 2 ]")
    {
      auto obj = make_interval(val2, val2, environment, ns);
      THEN_PREDICATE(obj, "x == 2");
    }
    WHEN("[ 0, 2 ]")
    {
      auto obj = make_interval(val0, val2, environment, ns);
      THEN_PREDICATE(obj, "0 <= x && x <= 2");
    }
  }
}
