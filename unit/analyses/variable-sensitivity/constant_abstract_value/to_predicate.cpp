/*******************************************************************\

 Module: Tests for constant_abstract_valuet::to_predicate

 Author: Jez Higgins

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/namespace.h>

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <testing-utils/empty_namespace.h>
#include <testing-utils/use_catch.h>

SCENARIO(
  "constant_abstract_value to predicate",
  "[core][analyses][variable-sensitivity][constant_abstract_value][to_"
  "predicate]")
{
  const typet type = signedbv_typet(32);
  const exprt val2 = from_integer(2, type);

  const exprt x_name = symbol_exprt("x", type);

  auto config = vsd_configt::constant_domain();
  config.context_tracking.data_dependency_context = false;
  config.context_tracking.last_write_context = false;
  auto object_factory =
    variable_sensitivity_object_factoryt::configured_with(config);
  abstract_environmentt environment{object_factory};
  environment.make_top();

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
      auto obj = make_constant(val2, environment, empty_namespace);
      THEN_PREDICATE(obj, "x == 2");
    }
    WHEN("(1 + 2) = 3")
    {
      auto val1 = from_integer(1, type);
      auto c3 =
        make_constant(from_integer(3, type), environment, empty_namespace);

      auto pred = c3->to_predicate(plus_exprt(val1, val2));
      THEN("predicate is (1 + 2) = 3")
      {
        auto repr = expr_to_str(pred);
        REQUIRE(repr == "1 + 2 == 3");
      }
    }
  }
}
