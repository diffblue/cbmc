/*******************************************************************\

 Module: Unit tests for value_set_abstract_valuet::merge

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <ansi-c/ansi_c_language.h>
#include <testing-utils/use_catch.h>
#include <util/arith_tools.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

static std::shared_ptr<value_set_abstract_objectt>
make_value_set(exprt val, abstract_environmentt &env, namespacet &ns);

static std::shared_ptr<const constant_abstract_valuet>
make_constant(exprt val, abstract_environmentt &env, namespacet &ns);

static std::shared_ptr<value_set_abstract_objectt> make_value_set(
  const std::vector<exprt> &vals,
  abstract_environmentt &env,
  namespacet &ns);

static std::shared_ptr<const value_set_abstract_objectt>
as_value_set(const abstract_object_pointert &aop);

static bool set_contains(const abstract_object_sett &set, const exprt &val);

static void EXPECT(
  std::shared_ptr<const value_set_abstract_objectt> &result,
  const std::vector<exprt> &expected_values);

static void
EXPECT_TOP(std::shared_ptr<const value_set_abstract_objectt> &result);

static void EXPECT_UNMODIFIED(
  std::shared_ptr<const value_set_abstract_objectt> &result,
  bool modified,
  const std::vector<exprt> &expected_values);

SCENARIO(
  "merging two value_set_abstract_objects",
  "[core][analyses][variable-sensitivity][value_set_abstract_object][merge]")
{
  GIVEN("Two value sets")
  {
    const exprt val1 = from_integer(1, integer_typet());
    const exprt val2 = from_integer(2, integer_typet());
    const exprt val3 = from_integer(3, integer_typet());
    const exprt val4 = from_integer(4, integer_typet());

    auto object_factory = variable_sensitivity_object_factoryt::configured_with(
      vsd_configt::value_set());
    auto environment = abstract_environmentt{object_factory};
    environment.make_top();
    auto symbol_table = symbol_tablet{};
    auto ns = namespacet{symbol_table};

    WHEN("merging { 1 } with { 1 }")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_value_set(val1, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result { 1 } is unchanged ")
      {
        EXPECT_UNMODIFIED(value_set_result, modified, {val1});
      }
    }

    WHEN("merging { 1 } with { 2 }")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_value_set(val2, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is { 1, 2 }")
      {
        EXPECT(value_set_result, {val1, val2});
      }
    }

    WHEN("merging { 1, 2 } with { 2 }")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set(val2, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result { 1, 2 } is unchanged")
      {
        EXPECT_UNMODIFIED(value_set_result, modified, {val1, val2});
      }
    }

    WHEN("merging { 1, 2 } with { 3, 4 }")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_value_set({val3, val4}, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is { 1, 2, 3, 4 }")
      {
        EXPECT(value_set_result, {val1, val2, val3, val4});
      }
    }

    WHEN("merging { 1, 2, 3 } with { 1, 3, 4 }")
    {
      auto op1 = make_value_set({val1, val2, val3}, environment, ns);
      auto op2 = make_value_set({val1, val3, val4}, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is { 1, 2, 3, 4 }")
      {
        EXPECT(value_set_result, {val1, val2, val3, val4});
      }
    }
  }
}

SCENARIO(
  "merging a value_set with a constant",
  "[core][analyses][variable-sensitivity][value_set_abstract_object][merge]")
{
  GIVEN("A value set and a constant")
  {
    const exprt val1 = from_integer(1, integer_typet());
    const exprt val2 = from_integer(2, integer_typet());
    const exprt val3 = from_integer(3, integer_typet());
    const exprt val4 = from_integer(4, integer_typet());

    auto object_factory = variable_sensitivity_object_factoryt::configured_with(
      vsd_configt::value_set());
    auto environment = abstract_environmentt{object_factory};
    environment.make_top();
    auto symbol_table = symbol_tablet{};
    auto ns = namespacet{symbol_table};

    WHEN("merging { 1 } with 1")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_constant(val1, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result { 1 } is unchanged ")
      {
        EXPECT_UNMODIFIED(value_set_result, modified, {val1});
      }
    }

    WHEN("merging { 1 } with 2")
    {
      auto op1 = make_value_set(val1, environment, ns);
      auto op2 = make_constant(val2, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is { 1, 2 }")
      {
        EXPECT(value_set_result, {val1, val2});
      }
    }

    WHEN("merging { 1, 2 } with 2")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = make_constant(val2, environment, ns);

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result { 1, 2 } is unchanged")
      {
        EXPECT_UNMODIFIED(value_set_result, modified, {val1, val2});
      }
    }
  }
}

SCENARIO(
  "merging a value_set with a TOP value",
  "[core][analyses][variable-sensitivity][value_set_abstract_object][merge]")
{
  GIVEN("A value set and a TOP constant")
  {
    const exprt val1 = from_integer(1, integer_typet());
    const exprt val2 = from_integer(2, integer_typet());

    auto object_factory = variable_sensitivity_object_factoryt::configured_with(
      vsd_configt::value_set());
    auto environment = abstract_environmentt{object_factory};
    environment.make_top();
    auto symbol_table = symbol_tablet{};
    auto ns = namespacet{symbol_table};

    WHEN("merging { 1, 2 } with TOP constant")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = std::make_shared<constant_abstract_valuet>(val1.type());
      REQUIRE(op2->is_top());

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is top")
      {
        EXPECT_TOP(value_set_result);
      }
    }

    WHEN("merging { 1, 2 } with TOP interval")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 =
        std::make_shared<interval_abstract_valuet>(unsignedbv_typet(32));
      REQUIRE(op2->is_top());

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is top")
      {
        EXPECT_TOP(value_set_result);
      }
    }

    WHEN("merging { 1, 2 } with TOP value-set")
    {
      auto op1 = make_value_set({val1, val2}, environment, ns);
      auto op2 = std::make_shared<value_set_abstract_objectt>(val1.type());
      REQUIRE(op2->is_top());

      bool modified;
      auto result = abstract_objectt::merge(op1, op2, modified);

      auto value_set_result = as_value_set(result);

      THEN("the result is top")
      {
        EXPECT_TOP(value_set_result);
      }
    }
  }
}

static std::shared_ptr<value_set_abstract_objectt>
make_value_set(exprt val, abstract_environmentt &env, namespacet &ns)
{
  return std::make_shared<value_set_abstract_objectt>(val, env, ns);
}

static std::shared_ptr<const constant_abstract_valuet>
make_constant(exprt val, abstract_environmentt &env, namespacet &ns)
{
  return std::make_shared<constant_abstract_valuet>(val, env, ns);
}

static std::shared_ptr<value_set_abstract_objectt> make_value_set(
  const std::vector<exprt> &vals,
  abstract_environmentt &env,
  namespacet &ns)
{
  auto initial_values = abstract_object_sett{};
  for(auto v : vals)
    initial_values.insert(make_constant(v, env, ns));
  auto vs = make_value_set(vals[0], env, ns);
  vs->set_values(initial_values);
  return vs;
}

static std::shared_ptr<const value_set_abstract_objectt>
as_value_set(const abstract_object_pointert &aop)
{
  return std::dynamic_pointer_cast<const value_set_abstract_objectt>(aop);
}

static bool set_contains(const abstract_object_sett &set, const exprt &val)
{
  auto i = std::find_if(
    set.begin(), set.end(), [&val](const abstract_object_pointert &lhs) {
      auto l = lhs->to_constant();
      return l == val;
    });
  return i != set.end();
}

static std::string expr_to_str(const exprt &expr)
{
  auto st = symbol_tablet{};
  auto ns = namespacet{st};
  auto expr_str = std::string{};

  auto lang = new_ansi_c_language();
  lang->from_expr(expr, expr_str, ns);

  return expr_str;
}

static void EXPECT(
  std::shared_ptr<const value_set_abstract_objectt> &result,
  const std::vector<exprt> &expected_values)
{
  REQUIRE(result);

  // Correctness of merge
  REQUIRE_FALSE(result->is_top());
  REQUIRE_FALSE(result->is_bottom());

  auto values = result->get_values();
  REQUIRE(values.size() == expected_values.size());

  for(auto &ev : expected_values)
  {
    INFO("Expect result to include " + expr_to_str(ev));
    REQUIRE(set_contains(values, ev));
  }
}

static void EXPECT_UNMODIFIED(
  std::shared_ptr<const value_set_abstract_objectt> &result,
  bool modified,
  const std::vector<exprt> &expected_values)
{
  CHECK_FALSE(modified);
  EXPECT(result, expected_values);
}

static void
EXPECT_TOP(std::shared_ptr<const value_set_abstract_objectt> &result)
{
  REQUIRE(result);

  REQUIRE(result->is_top());
  REQUIRE_FALSE(result->is_bottom());

  auto values = result->get_values();
  REQUIRE(values.empty());
}
