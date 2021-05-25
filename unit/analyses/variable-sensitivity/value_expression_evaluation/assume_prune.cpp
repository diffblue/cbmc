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
  auto val3 = from_integer(3, type);
  auto val4 = from_integer(4, type);
  auto val5 = from_integer(5, type);

  auto v12 = make_value_set({val1, val2}, environment, ns);
  auto v13 = make_value_set({val1, val3}, environment, ns);
  auto v23 = make_value_set({val2, val3}, environment, ns);
  auto v15 = make_value_set({val1, val5}, environment, ns);
  auto v25 = make_value_set({val2, val5}, environment, ns);

  auto i12 = make_interval(val1, val2, environment, ns);
  auto i13 = make_interval(val1, val3, environment, ns);
  auto i23 = make_interval(val2, val3, environment, ns);
  auto i15 = make_interval(val1, val5, environment, ns);
  auto i25 = make_interval(val2, val5, environment, ns);

  auto x = symbol_exprt("x", type);
  auto y = symbol_exprt("y", type);

  WHEN("x == y when x = { 1, 2 }, y = { 2, 5 }")
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
  WHEN("x == y when x = [ 1, 2 ], y = [ 2, 5 ]")
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
  WHEN("x == y when x = { 1, 2 }, y = [ 2, 5 ]")
  {
    environment.assign(x, v12, ns);
    environment.assign(y, i25, ns);

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
  WHEN("x == y when x = [ 1, 2 ], y = { 2, 5 }")
  {
    environment.assign(x, i12, ns);
    environment.assign(y, v25, ns);

    THEN("x == y and their values are pruned to [ 2 ]")
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

  WHEN(" x < y when x = { 1, 3 }, y = { 2, 5 }")
  {
    environment.assign(x, v13, ns);
    environment.assign(y, v25, ns);

    THEN("x < y and x and y are unchanged")
    {
      auto assumption =
        environment.do_assume(binary_relation_exprt(x, ID_lt, y), ns);
      REQUIRE(assumption.id() != ID_nil);
      REQUIRE(assumption.type().id() == ID_bool);
      REQUIRE(assumption.is_true());

      auto lhs_result = as_value_set(environment.eval(x, ns));
      auto rhs_result = as_value_set(environment.eval(y, ns));

      EXPECT(lhs_result, {val1, val3});
      EXPECT(rhs_result, {val2, val5});
    }
  }
  WHEN(" x < y when x = { 2, 3 }, y = { 1, 5 }")
  {
    environment.assign(x, v23, ns);
    environment.assign(y, v15, ns);

    THEN("x < y and y lower bound is pruned")
    {
      auto assumption =
        environment.do_assume(binary_relation_exprt(x, ID_lt, y), ns);
      REQUIRE(assumption.id() != ID_nil);
      REQUIRE(assumption.type().id() == ID_bool);
      REQUIRE(assumption.is_true());

      auto lhs_result = as_value_set(environment.eval(x, ns));
      auto rhs_result = as_value_set(environment.eval(y, ns));

      EXPECT(lhs_result, {val2, val3});
      EXPECT(rhs_result, {val5});
    }
  }
  WHEN(" x < y when x = { 1, 5 }, y = { 2, 3 }")
  {
    environment.assign(x, v15, ns);
    environment.assign(y, v23, ns);

    THEN("x < y and x upper bound is pruned")
    {
      auto assumption =
        environment.do_assume(binary_relation_exprt(x, ID_lt, y), ns);
      REQUIRE(assumption.id() != ID_nil);
      REQUIRE(assumption.type().id() == ID_bool);
      REQUIRE(assumption.is_true());

      auto lhs_result = as_value_set(environment.eval(x, ns));
      auto rhs_result = as_value_set(environment.eval(y, ns));

      EXPECT(lhs_result, {val1});
      EXPECT(rhs_result, {val2, val3});
    }
  }
  WHEN(" x < y when x = { 2, 5 }, y = { 1, 3 }")
  {
    environment.assign(x, v25, ns);
    environment.assign(y, v13, ns);

    THEN("x < y and x upper bound is pruned, y lower bound is pruned")
    {
      auto assumption =
        environment.do_assume(binary_relation_exprt(x, ID_lt, y), ns);
      REQUIRE(assumption.id() != ID_nil);
      REQUIRE(assumption.type().id() == ID_bool);
      REQUIRE(assumption.is_true());

      auto lhs_result = as_value_set(environment.eval(x, ns));
      auto rhs_result = as_value_set(environment.eval(y, ns));

      EXPECT(lhs_result, {val2});
      EXPECT(rhs_result, {val3});
    }
  }
  WHEN(" x < y when x = [ 1, 3 ], y = [ 2, 5 ]")
  {
    environment.assign(x, i13, ns);
    environment.assign(y, i25, ns);

    THEN("x < y and x and y are unchanged")
    {
      auto assumption =
        environment.do_assume(binary_relation_exprt(x, ID_lt, y), ns);
      REQUIRE(assumption.id() != ID_nil);
      REQUIRE(assumption.type().id() == ID_bool);
      REQUIRE(assumption.is_true());

      auto lhs_result = as_interval(environment.eval(x, ns));
      auto rhs_result = as_interval(environment.eval(y, ns));

      EXPECT(lhs_result, val1, val3);
      EXPECT(rhs_result, val2, val5);
    }
  }
  WHEN(" x < y when x = [ 2, 3 ], y = [ 1, 5 ]")
  {
    environment.assign(x, i23, ns);
    environment.assign(y, i15, ns);

    THEN("x < y and y lower bound is pruned")
    {
      auto assumption =
        environment.do_assume(binary_relation_exprt(x, ID_lt, y), ns);
      REQUIRE(assumption.id() != ID_nil);
      REQUIRE(assumption.type().id() == ID_bool);
      REQUIRE(assumption.is_true());

      auto lhs_result = as_interval(environment.eval(x, ns));
      auto rhs_result = as_interval(environment.eval(y, ns));

      EXPECT(lhs_result, val2, val3);
      EXPECT(rhs_result, val2, val5);
    }
  }
  WHEN(" x < y when x = [ 1, 5 ], y = [ 2, 3 ]")
  {
    environment.assign(x, i15, ns);
    environment.assign(y, i23, ns);

    THEN("x < y and x upper bound is pruned")
    {
      auto assumption =
        environment.do_assume(binary_relation_exprt(x, ID_lt, y), ns);
      REQUIRE(assumption.id() != ID_nil);
      REQUIRE(assumption.type().id() == ID_bool);
      REQUIRE(assumption.is_true());

      auto lhs_result = as_interval(environment.eval(x, ns));
      auto rhs_result = as_interval(environment.eval(y, ns));

      EXPECT(lhs_result, val1, val3);
      EXPECT(rhs_result, val2, val3);
    }
  }
  WHEN(" x < y when x = [ 2, 5 ], y = [ 1, 3 ]")
  {
    environment.assign(x, i25, ns);
    environment.assign(y, i13, ns);

    THEN("x < y and x upper bound is pruned, u lower bound is pruned")
    {
      auto assumption =
        environment.do_assume(binary_relation_exprt(x, ID_lt, y), ns);
      REQUIRE(assumption.id() != ID_nil);
      REQUIRE(assumption.type().id() == ID_bool);
      REQUIRE(assumption.is_true());

      auto lhs_result = as_interval(environment.eval(x, ns));
      auto rhs_result = as_interval(environment.eval(y, ns));

      EXPECT(lhs_result, val2, val3);
      EXPECT(rhs_result, val2, val3);
    }
  }

  WHEN(" x < y when x = { 2, 3 }, y = { 1, [2, 5] }")
  {
    auto v1i25 = make_value_set(
      {val1, constant_interval_exprt(val2, val5)}, environment, ns);
    environment.assign(x, v23, ns);
    environment.assign(y, v1i25, ns);

    THEN("x < y and y lower bound is pruned")
    {
      auto assumption =
        environment.do_assume(binary_relation_exprt(x, ID_lt, y), ns);
      REQUIRE(assumption.id() != ID_nil);
      REQUIRE(assumption.type().id() == ID_bool);
      REQUIRE(assumption.is_true());

      auto lhs_result = as_value_set(environment.eval(x, ns));
      auto rhs_result = as_value_set(environment.eval(y, ns));

      EXPECT(lhs_result, {val2, val3});
      EXPECT(rhs_result, {constant_interval_exprt(val2, val5)});
    }
  }
  WHEN(" x < y when x = { 1, [2, 5] }, y = { 2, 3 }")
  {
    auto v1i25 = make_value_set(
      {val1, constant_interval_exprt(val2, val5)}, environment, ns);
    environment.assign(x, v1i25, ns);
    environment.assign(y, v23, ns);

    THEN("x < y and x upper bound is pruned")
    {
      auto assumption =
        environment.do_assume(binary_relation_exprt(x, ID_lt, y), ns);
      REQUIRE(assumption.id() != ID_nil);
      REQUIRE(assumption.type().id() == ID_bool);
      REQUIRE(assumption.is_true());

      auto lhs_result = as_value_set(environment.eval(x, ns));
      auto rhs_result = as_value_set(environment.eval(y, ns));

      EXPECT(lhs_result, {val1, constant_interval_exprt(val2, val3)});
      EXPECT(rhs_result, {val2, val3});
    }
  }
  WHEN(" x < y when x = { [2, 4], 5 }, y = { 1, [2, 3] }")
  {
    auto i24v5 = make_value_set(
      {val5, constant_interval_exprt(val2, val4)}, environment, ns);
    environment.assign(x, i24v5, ns);
    auto v1i23 = make_value_set(
      {val1, constant_interval_exprt(val2, val3)}, environment, ns);
    environment.assign(y, v1i23, ns);

    THEN("x < y and x upper bound is pruned, y lower bound is pruned")
    {
      auto assumption =
        environment.do_assume(binary_relation_exprt(x, ID_lt, y), ns);
      REQUIRE(assumption.id() != ID_nil);
      REQUIRE(assumption.type().id() == ID_bool);
      REQUIRE(assumption.is_true());

      auto lhs_result = as_value_set(environment.eval(x, ns));
      auto rhs_result = as_value_set(environment.eval(y, ns));

      EXPECT(lhs_result, {constant_interval_exprt(val2, val3)});
      EXPECT(rhs_result, {constant_interval_exprt(val2, val3)});
    }
  }
}
