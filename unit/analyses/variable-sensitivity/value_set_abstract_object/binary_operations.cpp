/*******************************************************************\

 Module: Unit tests for value_set_abstract_valuet::expression_transform

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

static std::shared_ptr<const value_set_abstract_objectt>
as_value_set(const abstract_object_pointert &aop);

static bool set_contains(const abstract_object_sett &set, const exprt &val);

static void EXPECT(
  std::shared_ptr<const value_set_abstract_objectt> &result,
  const std::vector<exprt> &expected_values);

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

static std::shared_ptr<value_set_abstract_objectt>
make_value_set(exprt val, abstract_environmentt &env, namespacet &ns)
{
  return std::make_shared<value_set_abstract_objectt>(val, env, ns);
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
