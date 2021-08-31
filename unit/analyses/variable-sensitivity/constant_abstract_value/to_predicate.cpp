/*******************************************************************\

 Module: Tests for constant_abstract_valuet::to_predicate

 Author: Jez Higgins

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/symbol_table.h>

SCENARIO(
  "constant_abstract_value to predicate",
  "[core][analyses][variable-sensitivity][constant_abstract_value][to_"
  "predicate]")
{
  const typet type = signedbv_typet(32);
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

  GIVEN("constant_abstract_value")
  {
    WHEN("it is TOP")
    {
      auto obj = make_top_constant();
      THEN_PREDICATE(obj, "TRUE");
    }
    WHEN("it is BOTTOM")
    {
      auto obj = make_bottom_constant();
      THEN_PREDICATE(obj, "FALSE");
    }
    WHEN("x = 2")
    {
      auto obj = make_constant(val2, environment, ns);
      THEN_PREDICATE(obj, "x == 2");
    }
    WHEN("(1 + 2) = 3")
    {
      auto val1 = from_integer(1, type);
      auto c3 = make_constant(from_integer(3, type), environment, ns);

      auto pred = c3->to_predicate(plus_exprt(val1, val2));
      THEN("predicate is (1 + 2) = 3")
      {
        auto repr = expr_to_str(pred);
        REQUIRE(repr == "1 + 2 == 3");
      }
    }
  }
}
