/*******************************************************************\

 Module: Unit tests for abstract_value_objectt::expression_transform

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>

template <class expression_type>
exprt binary_expression(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2,
  abstract_environmentt &environment,
  namespacet &ns)
{
  auto op1_sym = symbol_exprt("op1", op1->type());
  auto op2_sym = symbol_exprt("op2", op2->type());
  environment.assign(op1_sym, op1, ns);
  environment.assign(op2_sym, op2, ns);

  return expression_type(op1_sym, op2_sym);
}

static exprt compare_equal(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2,
  abstract_environmentt &environment,
  namespacet &ns)
{
  return binary_expression<equal_exprt>(op1, op2, environment, ns);
}

static void ASSUME_TRUE(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns);
static void ASSUME_FALSE(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns);

SCENARIO(
  "assume value expressions",
  "[core][analyses][variable-sensitivity][constant_abstract_value][value_set_"
  "abstract_object][interval_abstract_value][assume]")
{
  const typet type = signedbv_typet(32);
  const exprt val1 = from_integer(1, type);
  const exprt val2 = from_integer(2, type);
  const exprt val3 = from_integer(3, type);
  const exprt val4 = from_integer(4, type);
  const exprt val5 = from_integer(5, type);

  auto config = vsd_configt::constant_domain();
  config.context_tracking.data_dependency_context = false;
  config.context_tracking.last_write_context = false;
  auto object_factory =
    variable_sensitivity_object_factoryt::configured_with(config);
  abstract_environmentt environment{object_factory};
  environment.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("expected equal")
  {
    WHEN("2 == 2")
    {
      auto op1 = make_constant(val2, environment, ns);
      auto op2 = make_constant(val2, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("[1, 1] == 1")
    {
      auto op1 = make_interval(val1, val1, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("[1, 1] == [1, 1]")
    {
      auto op1 = make_interval(val1, val1, environment, ns);
      auto op2 = make_interval(val1, val1, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("[1, 1] == { 1 }")
    {
      auto op1 = make_interval(val1, val1, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("[1, 2] == 1")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("[1, 2] == [1, 1]")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_interval(val1, val1, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("[1, 2] == { 1 }")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("[1, 2] == 2")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_constant(val2, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("[1, 2] == [2, 2]")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_interval(val2, val2, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("[1, 2] == [1, 2]")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_interval(val1, val2, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("[1, 2] == {1, 2}")
    {
      auto op1 = make_interval(val1, val2, environment, ns);
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("[1, 3] == 2")
    {
      auto op1 = make_interval(val1, val3, environment, ns);
      auto op2 = make_constant(val2, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("[1, 3] == [2, 2]")
    {
      auto op1 = make_interval(val1, val3, environment, ns);
      auto op2 = make_interval(val2, val2, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("[1, 3] == { 2 }")
    {
      auto op1 = make_interval(val1, val3, environment, ns);
      auto op2 = make_value_set(val2, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("{ 1 } == 1")
    {
      auto op1 = make_value_set({val1}, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("{ 1, 2 } == 1")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("{ 1, 2 } == [ 1 ]")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_interval(val1, val1, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("{ 1, 2 } == [ 1, 2 ]")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_interval(val1, val3, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("{ 1, 2 } == [ 1, 3 ]")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_interval(val1, val3, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("{ 1, 2 } == [ 2, 5 ]")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_interval(val2, val5, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("{ 1, 2 } == { 1 }")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set({val1, val1}, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("{ 1, 2 } == { 1, 2 }")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set({val1, val2}, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("{ 1, 2 } == { 1, 3 }")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set({val1, val3}, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
    WHEN("{ 1, 2 } == { 2, 5 }")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set({val2, val5}, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_TRUE(environment, equals, ns);
    }
  }

  GIVEN("expected not equal")
  {
    WHEN("1 == 2")
    {
      auto op1 = make_constant(val1, environment, ns);
      auto op2 = make_constant(val2, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_FALSE(environment, equals, ns);
    }
    WHEN("[2, 3] == 1")
    {
      auto op1 = make_interval(val2, val3, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_FALSE(environment, equals, ns);
    }
    WHEN("[2, 3] == [1, 1]")
    {
      auto op1 = make_interval(val2, val3, environment, ns);
      auto op2 = make_interval(val1, val1, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_FALSE(environment, equals, ns);
    }
    WHEN("{ 2, 3 } == 1")
    {
      auto op1 = make_value_set({val2, val3}, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_FALSE(environment, equals, ns);
    }
    WHEN("{ 2, 3 } == { 4, 5 }")
    {
      auto op1 = make_value_set({val2, val3}, environment, ns);
      auto op2 = make_value_set({val4, val5}, environment, ns);

      auto equals = compare_equal(op1, op2, environment, ns);

      ASSUME_FALSE(environment, equals, ns);
    }
  }
}

void ASSUME_TRUE(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns)
{
  THEN("assume is true")
  {
    auto assumption = env.do_assume(expr, ns, true);
    REQUIRE(assumption.id() != ID_nil);
    REQUIRE(assumption.type().id() == ID_bool);
    REQUIRE(assumption.is_true());
  }
}

void ASSUME_FALSE(
  abstract_environmentt &env,
  const exprt &expr,
  const namespacet &ns)
{
  THEN("assume is false")
  {
    auto assumption = env.do_assume(expr, ns, true);
    REQUIRE(assumption.id() != ID_nil);
    REQUIRE(assumption.type().id() == ID_bool);
    REQUIRE(assumption.is_false());
  }
}
