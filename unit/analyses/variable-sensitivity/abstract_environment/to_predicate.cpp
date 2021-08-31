/*******************************************************************\

 Module: Tests for abstract_environmentt::to_predicate

 Author: Jez Higgins

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>
#include <util/symbol_table.h>

SCENARIO(
  "abstract_environment to predicate",
  "[core][analyses][variable-sensitivity][abstract_environment][to_predicate]")
{
  auto config = vsd_configt::constant_domain();
  config.context_tracking.data_dependency_context = false;
  config.context_tracking.last_write_context = false;
  auto object_factory =
    variable_sensitivity_object_factoryt::configured_with(config);
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("an abstract environment")
  {
    WHEN("it is TOP")
    {
      auto env = abstract_environmentt{object_factory};
      env.make_top();
      THEN_PREDICATE(env, "TRUE");
    }
    WHEN("it is BOTTOM")
    {
      auto env = abstract_environmentt{object_factory};
      env.make_bottom();
      THEN_PREDICATE(env, "FALSE");
    }
    WHEN("contains x = 2")
    {
      auto env = abstract_environmentt{object_factory};
      env.make_top();

      auto type = signedbv_typet(32);
      auto val2 = make_constant(from_integer(2, type), env, ns);
      auto x_name = symbol_exprt(dstringt("x"), type);

      env.assign(x_name, val2, ns);

      THEN_PREDICATE(env, "x == 2");
    }
    WHEN("contains x = 2, y = 3")
    {
      auto env = abstract_environmentt{object_factory};
      env.make_top();

      auto type = signedbv_typet(32);
      auto val2 = make_constant(from_integer(2, type), env, ns);
      auto x_name = symbol_exprt(dstringt("x"), type);

      auto val3 = make_constant(from_integer(3, type), env, ns);
      auto y_name = symbol_exprt(dstringt("y"), type);

      env.assign(x_name, val2, ns);
      env.assign(y_name, val3, ns);

      THEN_PREDICATE(env, "x == 2 && y == 3");
    }
  }
}
