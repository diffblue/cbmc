/*******************************************************************\

 Module: Unit tests for value_set_abstract_valuet::expression_transform

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include "value_set_test_helpers.h"
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <testing-utils/use_catch.h>
#include <util/arith_tools.h>
#include <util/mathematical_types.h>

SCENARIO(
  "adding two value_set_abstract_objects",
  "[core][analyses][variable-sensitivity][value_set_abstract_object][merge]")
{
  GIVEN("Two value sets")
  {
    const exprt val1 = from_integer(1, integer_typet());
    const exprt val2 = from_integer(2, integer_typet());
    const exprt val3 = from_integer(3, integer_typet());
    const exprt val4 = from_integer(4, integer_typet());

    auto config = vsd_configt::value_set();
    config.context_tracking.data_dependency_context = false;
    config.context_tracking.last_write_context = false;
    auto object_factory =
      variable_sensitivity_object_factoryt::configured_with(config);
    auto environment = abstract_environmentt{object_factory};
    environment.make_top();
    auto symbol_table = symbol_tablet{};
    auto ns = namespacet{symbol_table};

    WHEN("{ 1 } + { 1 }")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);

      auto op1_sym = symbol_exprt("op1", op1->type());
      auto op2_sym = symbol_exprt("op2", op2->type());
      environment.assign(op1_sym, op1, ns);
      environment.assign(op2_sym, op2, ns);

      auto result = environment.eval(plus_exprt(op1_sym, op2_sym), ns);

      auto value_set_result = as_value_set(result);

      THEN("= { 2 }")
      {
        EXPECT(value_set_result, {val2});
      }
    }
  }
}
