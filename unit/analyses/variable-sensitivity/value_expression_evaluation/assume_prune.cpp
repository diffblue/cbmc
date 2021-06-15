/*******************************************************************\

 Module: Unit tests for abstract_environmentt::assume pruning

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>

static void ASSUME_TRUE(
  symbol_exprt const &x,
  const irep_idt &id,
  symbol_exprt const &y,
  abstract_environmentt &env,
  namespacet &ns)
{
  auto assumption = env.do_assume(binary_relation_exprt(x, id, y), ns);

  REQUIRE(assumption.id() != ID_nil);
  REQUIRE(assumption.type().id() == ID_bool);
  REQUIRE(assumption.is_true());
}

static void EXPECT_RESULT(
  symbol_exprt const &x,
  const std::vector<exprt> &x_expected,
  symbol_exprt const &y,
  const std::vector<exprt> &y_expected,
  abstract_environmentt &env,
  namespacet &ns)
{
  auto x_result = as_value_set(env.eval(x, ns));
  auto y_result = as_value_set(env.eval(y, ns));

  EXPECT(x_result, x_expected);
  EXPECT(y_result, y_expected);
}

static void EXPECT_RESULT(
  symbol_exprt const &x,
  exprt const &x_lower,
  exprt const &x_upper,
  symbol_exprt const &y,
  exprt const &y_lower,
  exprt const &y_upper,
  abstract_environmentt &env,
  namespacet &ns)
{
  auto x_result = as_interval(env.eval(x, ns));
  auto y_result = as_interval(env.eval(y, ns));

  EXPECT(x_result, x_lower, x_upper);
  EXPECT(y_result, y_lower, y_upper);
}

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
  auto val0 = from_integer(0, type);
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
      ASSUME_TRUE(x, ID_equal, y, environment, ns);

      EXPECT_RESULT(x, {val2}, y, {val2}, environment, ns);
    }
  }
  WHEN("x == y when x = [ 1, 2 ], y = [ 2, 5 ]")
  {
    environment.assign(x, i12, ns);
    environment.assign(y, i25, ns);

    THEN("x == y and their values are pruned to [ 2 ]")
    {
      ASSUME_TRUE(x, ID_equal, y, environment, ns);

      EXPECT_RESULT(x, val2, val2, y, val2, val2, environment, ns);
    }
  }
  WHEN("x == y when x = { 1, 2 }, y = [ 2, 5 ]")
  {
    environment.assign(x, v12, ns);
    environment.assign(y, i25, ns);

    THEN("x == y and their values are pruned to { 2 }")
    {
      ASSUME_TRUE(x, ID_equal, y, environment, ns);

      EXPECT_RESULT(x, {val2}, y, {val2}, environment, ns);
    }
  }
  WHEN("x == y when x = [ 1, 2 ], y = { 2, 5 }")
  {
    environment.assign(x, i12, ns);
    environment.assign(y, v25, ns);

    THEN("x == y and their values are pruned to [ 2 ]")
    {
      ASSUME_TRUE(x, ID_equal, y, environment, ns);

      EXPECT_RESULT(x, val2, val2, y, val2, val2, environment, ns);
    }
  }
  WHEN("x == y when x = [ 1, 2 ], and y is TOP")
  {
    environment.assign(x, i12, ns);
    environment.assign(
      y, std::make_shared<constant_abstract_valuet>(y.type(), true, false), ns);

    THEN("x == y and their values are pruned to [ 1, 2 ]")
    {
      ASSUME_TRUE(x, ID_equal, y, environment, ns);

      EXPECT_RESULT(x, val1, val2, y, val1, val2, environment, ns);
    }
  }

  WHEN(" x < y when x = { 1, 3 }, y = { 2, 5 }")
  {
    environment.assign(x, v13, ns);
    environment.assign(y, v25, ns);

    THEN("x < y and x and y are unchanged")
    {
      ASSUME_TRUE(x, ID_lt, y, environment, ns);

      EXPECT_RESULT(x, {val1, val3}, y, {val2, val5}, environment, ns);
    }
  }
  WHEN(" x < y when x = { 2, 3 }, y = { 1, 5 }")
  {
    environment.assign(x, v23, ns);
    environment.assign(y, v15, ns);

    THEN("x < y and y lower bound is pruned")
    {
      ASSUME_TRUE(x, ID_lt, y, environment, ns);

      EXPECT_RESULT(x, {val2, val3}, y, {val5}, environment, ns);
    }
  }
  WHEN(" x < y when x = { 1, 5 }, y = { 2, 3 }")
  {
    environment.assign(x, v15, ns);
    environment.assign(y, v23, ns);

    THEN("x < y and x upper bound is pruned")
    {
      ASSUME_TRUE(x, ID_lt, y, environment, ns);

      EXPECT_RESULT(x, {val1}, y, {val2, val3}, environment, ns);
    }
  }
  WHEN(" x < y when x = { 2, 5 }, y = { 1, 3 }")
  {
    environment.assign(x, v25, ns);
    environment.assign(y, v13, ns);

    THEN("x < y and x upper bound is pruned, y lower bound is pruned")
    {
      ASSUME_TRUE(x, ID_lt, y, environment, ns);

      EXPECT_RESULT(x, {val2}, y, {val3}, environment, ns);
    }
  }
  WHEN(" x < y when x = [ 1, 3 ], y = [ 2, 5 ]")
  {
    environment.assign(x, i13, ns);
    environment.assign(y, i25, ns);

    THEN("x < y and x and y are unchanged")
    {
      ASSUME_TRUE(x, ID_lt, y, environment, ns);

      EXPECT_RESULT(x, val1, val3, y, val2, val5, environment, ns);
    }
  }
  WHEN(" x < y when x = [ 2, 3 ], y = [ 1, 5 ]")
  {
    environment.assign(x, i23, ns);
    environment.assign(y, i15, ns);

    THEN("x < y and y lower bound is pruned")
    {
      ASSUME_TRUE(x, ID_lt, y, environment, ns);

      EXPECT_RESULT(x, val2, val3, y, val2, val5, environment, ns);
    }
  }
  WHEN(" x < y when x = [ 1, 5 ], y = [ 2, 3 ]")
  {
    environment.assign(x, i15, ns);
    environment.assign(y, i23, ns);

    THEN("x < y and x upper bound is pruned")
    {
      ASSUME_TRUE(x, ID_lt, y, environment, ns);

      EXPECT_RESULT(x, val1, val3, y, val2, val3, environment, ns);
    }
  }
  WHEN(" x < y when x = [ 2, 5 ], y = [ 1, 3 ]")
  {
    environment.assign(x, i25, ns);
    environment.assign(y, i13, ns);

    THEN("x < y and x upper bound is pruned, u lower bound is pruned")
    {
      ASSUME_TRUE(x, ID_lt, y, environment, ns);

      EXPECT_RESULT(x, val2, val3, y, val2, val3, environment, ns);
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
      ASSUME_TRUE(x, ID_lt, y, environment, ns);

      EXPECT_RESULT(
        x,
        {val2, val3},
        y,
        {constant_interval_exprt(val2, val5)},
        environment,
        ns);
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
      ASSUME_TRUE(x, ID_lt, y, environment, ns);

      EXPECT_RESULT(
        x,
        {val1, constant_interval_exprt(val2, val3)},
        y,
        {val2, val3},
        environment,
        ns);
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
      ASSUME_TRUE(x, ID_lt, y, environment, ns);

      EXPECT_RESULT(
        x,
        {constant_interval_exprt(val2, val3)},
        y,
        {constant_interval_exprt(val2, val3)},
        environment,
        ns);
    }
  }

  WHEN(" x < y when x is TOP, y = [1, 5]")
  {
    auto top = std::make_shared<constant_abstract_valuet>(type, true, false);
    environment.assign(x, top, ns);
    environment.assign(y, i15, ns);

    THEN("x < y and x upper bound is pruned")
    {
      ASSUME_TRUE(x, ID_lt, y, environment, ns);

      EXPECT_RESULT(x, min_exprt(type), val5, y, val1, val5, environment, ns);
    }
  }

  WHEN(" x > y when x is [1, 5], y = TOP")
  {
    auto top = std::make_shared<constant_abstract_valuet>(type, true, false);
    environment.assign(x, i15, ns);
    environment.assign(y, top, ns);

    THEN("x < y and y lower bound is pruned")
    {
      ASSUME_TRUE(x, ID_lt, y, environment, ns);

      EXPECT_RESULT(x, val1, val5, y, val1, max_exprt(type), environment, ns);
    }
  }

  WHEN(" y > x when x = { 1, 3 }, y = { 2, 5 }")
  {
    environment.assign(x, v13, ns);
    environment.assign(y, v25, ns);

    THEN("y > x and x and y are unchanged")
    {
      ASSUME_TRUE(y, ID_gt, x, environment, ns);

      EXPECT_RESULT(x, {val1, val3}, y, {val2, val5}, environment, ns);
    }
  }
  WHEN(" y > x when x = { 2, 3 }, y = { 1, 5 }")
  {
    environment.assign(x, v23, ns);
    environment.assign(y, v15, ns);

    THEN("y > x and y lower bound is pruned")
    {
      ASSUME_TRUE(y, ID_gt, x, environment, ns);

      EXPECT_RESULT(x, {val2, val3}, y, {val5}, environment, ns);
    }
  }
  WHEN(" y > x when x = { 1, 5 }, y = { 2, 3 }")
  {
    environment.assign(x, v15, ns);
    environment.assign(y, v23, ns);

    THEN("y > x and x upper bound is pruned")
    {
      ASSUME_TRUE(y, ID_gt, x, environment, ns);

      EXPECT_RESULT(x, {val1}, y, {val2, val3}, environment, ns);
    }
  }
  WHEN(" y > x when x = { 2, 5 }, y = { 1, 3 }")
  {
    environment.assign(x, v25, ns);
    environment.assign(y, v13, ns);

    THEN("y > x and x upper bound is pruned, y lower bound is pruned")
    {
      ASSUME_TRUE(y, ID_gt, x, environment, ns);

      EXPECT_RESULT(x, {val2}, y, {val3}, environment, ns);
    }
  }

  WHEN(" y > x when x = [ 1, 3 ], y = [ 2, 5 ]")
  {
    environment.assign(x, i13, ns);
    environment.assign(y, i25, ns);

    THEN("y > x and x and y are unchanged")
    {
      ASSUME_TRUE(y, ID_gt, x, environment, ns);

      EXPECT_RESULT(x, val1, val3, y, val2, val5, environment, ns);
    }
  }
  WHEN(" y > x when x = [ 2, 3 ], y = [ 1, 5 ]")
  {
    environment.assign(x, i23, ns);
    environment.assign(y, i15, ns);

    THEN("y > x and y lower bound is pruned")
    {
      ASSUME_TRUE(y, ID_gt, x, environment, ns);

      EXPECT_RESULT(x, val2, val3, y, val2, val5, environment, ns);
    }
  }
  WHEN(" y > x when x = [ 1, 5 ], y = [ 2, 3 ]")
  {
    environment.assign(x, i15, ns);
    environment.assign(y, i23, ns);

    THEN("y > x and x upper bound is pruned")
    {
      ASSUME_TRUE(y, ID_gt, x, environment, ns);

      EXPECT_RESULT(x, val1, val3, y, val2, val3, environment, ns);
    }
  }
  WHEN(" y > x when x = [ 2, 5 ], y = [ 1, 3 ]")
  {
    environment.assign(x, i25, ns);
    environment.assign(y, i13, ns);

    THEN("y > x and x upper bound is pruned, u lower bound is pruned")
    {
      ASSUME_TRUE(y, ID_gt, x, environment, ns);

      EXPECT_RESULT(x, val2, val3, y, val2, val3, environment, ns);
    }
  }

  WHEN(" y > x when x = { 2, 3 }, y = { 1, [2, 5] }")
  {
    auto v1i25 = make_value_set(
      {val1, constant_interval_exprt(val2, val5)}, environment, ns);
    environment.assign(x, v23, ns);
    environment.assign(y, v1i25, ns);

    THEN("y > x and y lower bound is pruned")
    {
      ASSUME_TRUE(y, ID_gt, x, environment, ns);

      EXPECT_RESULT(
        x,
        {val2, val3},
        y,
        {constant_interval_exprt(val2, val5)},
        environment,
        ns);
    }
  }
  WHEN(" y > x when x = { 1, [2, 5] }, y = { 2, 3 }")
  {
    auto v1i25 = make_value_set(
      {val1, constant_interval_exprt(val2, val5)}, environment, ns);
    environment.assign(x, v1i25, ns);
    environment.assign(y, v23, ns);

    THEN("y > x and x upper bound is pruned")
    {
      ASSUME_TRUE(y, ID_gt, x, environment, ns);

      EXPECT_RESULT(
        x,
        {val1, constant_interval_exprt(val2, val3)},
        y,
        {val2, val3},
        environment,
        ns);
    }
  }
  WHEN(" y > x when x = { [2, 4], 5 }, y = { 1, [2, 3] }")
  {
    auto i24v5 = make_value_set(
      {val5, constant_interval_exprt(val2, val4)}, environment, ns);
    environment.assign(x, i24v5, ns);
    auto v1i23 = make_value_set(
      {val1, constant_interval_exprt(val2, val3)}, environment, ns);
    environment.assign(y, v1i23, ns);

    THEN("y > x and x upper bound is pruned, y lower bound is pruned")
    {
      ASSUME_TRUE(y, ID_gt, x, environment, ns);

      EXPECT_RESULT(
        x,
        {constant_interval_exprt(val2, val3)},
        y,
        {constant_interval_exprt(val2, val3)},
        environment,
        ns);
    }
  }

  WHEN(" y > x when x = { [2, 4], 5 }, y = { [0, 1], [2, 3] }")
  {
    auto i24v5 = make_value_set(
      {val5, constant_interval_exprt(val2, val4)}, environment, ns);
    environment.assign(x, i24v5, ns);
    auto i11i23 = make_value_set(
      {constant_interval_exprt(val0, val1),
       constant_interval_exprt(val2, val3)},
      environment,
      ns);
    environment.assign(y, i11i23, ns);

    THEN("y > x and x upper bound is pruned, y lower bound is pruned")
    {
      ASSUME_TRUE(y, ID_gt, x, environment, ns);

      EXPECT_RESULT(
        x,
        {constant_interval_exprt(val2, val3)},
        y,
        {constant_interval_exprt(val2, val3)},
        environment,
        ns);
    }
  }
}
