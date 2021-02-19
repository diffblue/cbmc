/*******************************************************************\

 Module: Unit tests for constant_abstract_valuet::expression_transform

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include "../variable_sensitivity_test_helpers.h"
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <testing-utils/use_catch.h>
#include <util/arith_tools.h>
#include <util/mathematical_types.h>

SCENARIO(
  "constants expression evaluation",
  "[core][analyses][variable-sensitivity][constant_abstract_value][expression_"
  "transform]")
{
  const exprt val1 = from_integer(1, integer_typet());
  const exprt val2 = from_integer(2, integer_typet());
  const exprt val3 = from_integer(3, integer_typet());

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
    WHEN("1 + TOP")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_constant(val2, true);
      auto result = add_as_constant(op1, op2, environment, ns);

      THEN("= TOP")
      {
        EXPECT_TOP(result);
      }
    }
    WHEN("TOP + 1")
    {
      auto op1 = make_constant(val1, true);
      auto op2 = make_constant(val2, environment, ns);
      auto result = add_as_constant(op1, op2, environment, ns);

      THEN("= TOP")
      {
        EXPECT_TOP(result);
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
  }
}
