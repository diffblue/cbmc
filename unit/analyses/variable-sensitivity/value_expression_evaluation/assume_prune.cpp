/*******************************************************************\

 Module: Unit tests for abstract_environmentt::assume pruning

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>

SCENARIO(
  "assume value expressions, pruning",
  "[core][analyses][variable-sensitivity][constant_abstract_value][value_set_"
  "abstract_object][interval_abstract_value][assume]")
{
  auto config = vsd_configt::constant_domain();
  config.context_tracking.data_dependency_context = false;
  config.context_tracking.last_write_context = false;
  auto object_factory =
    variable_sensitivity_object_factoryt::configured_with(config);
  abstract_environmentt environment{object_factory};
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  auto type = signedbv_typet(32);
  auto val1 = from_integer(1, type);
  auto val2 = from_integer(2, type);
  auto val5 = from_integer(5, type);
  auto v12 = make_value_set({val1, val2}, environment, ns);
  auto v25 = make_value_set({val2, val5}, environment, ns);
  auto i12 = make_interval(val1, val2, environment, ns);
  auto i25 = make_interval(val2, val5, environment, ns);

  auto x = symbol_exprt("x", type);
  auto y = symbol_exprt("y", type);

  WHEN("x = { 1, 2 }, y = { 2, 5 } then x == y, x & y are pruned")
  {
    environment.assign(x, v12, ns);
    environment.assign(y, v25, ns);

    THEN("x == y and their values are pruned to { 2 }")
    {
      auto assumption = environment.do_assume(equal_exprt(x, y), ns);
      REQUIRE(assumption.id() != ID_nil);
      REQUIRE(assumption.type().id() == ID_bool);
      REQUIRE(assumption.is_true());

      auto lhs_result = as_value_set(environment.eval(x, ns));
      auto rhs_result = as_value_set(environment.eval(y, ns));

      EXPECT(lhs_result, {val2});
      EXPECT(rhs_result, {val2});
    }
  }
  WHEN("x = [ 1, 2 ], y = [ 2, 5 ] then x == y, x & y are pruned")
  {
    environment.assign(x, i12, ns);
    environment.assign(y, i25, ns);

    THEN("x == y and their values are pruned to { 2 }")
    {
      auto assumption = environment.do_assume(equal_exprt(x, y), ns);
      REQUIRE(assumption.id() != ID_nil);
      REQUIRE(assumption.type().id() == ID_bool);
      REQUIRE(assumption.is_true());

      auto lhs_result = as_interval(environment.eval(x, ns));
      auto rhs_result = as_interval(environment.eval(y, ns));

      EXPECT(lhs_result, val2, val2);
      EXPECT(rhs_result, val2, val2);
    }
  }
}
