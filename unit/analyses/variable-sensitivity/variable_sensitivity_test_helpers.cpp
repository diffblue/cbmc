/*******************************************************************\

 Module: Unit tests helpers for abstract objects

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include "variable_sensitivity_test_helpers.h"
#include <analyses/variable-sensitivity/abstract_environment.h>
#include <ansi-c/ansi_c_language.h>
#include <testing-utils/use_catch.h>
#include <util/string_utils.h>

std::shared_ptr<value_set_abstract_objectt>
make_value_set(exprt val, abstract_environmentt &env, namespacet &ns)
{
  return std::make_shared<value_set_abstract_objectt>(val, env, ns);
}

std::shared_ptr<const constant_abstract_valuet>
make_constant(exprt val, abstract_environmentt &env, namespacet &ns)
{
  return std::make_shared<constant_abstract_valuet>(val, env, ns);
}

std::shared_ptr<const constant_abstract_valuet>
make_constant(exprt val, bool top)
{
  return std::make_shared<constant_abstract_valuet>(val.type(), top, !top);
}

std::shared_ptr<value_set_abstract_objectt> make_value_set(
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

std::shared_ptr<const constant_abstract_valuet>
as_constant(const abstract_object_pointert &aop)
{
  return std::dynamic_pointer_cast<const constant_abstract_valuet>(aop);
}

std::shared_ptr<const value_set_abstract_objectt>
as_value_set(const abstract_object_pointert &aop)
{
  return std::dynamic_pointer_cast<const value_set_abstract_objectt>(aop);
}

bool set_contains(const abstract_object_sett &set, const exprt &val)
{
  auto i = std::find_if(
    set.begin(), set.end(), [&val](const abstract_object_pointert &lhs) {
      auto l = lhs->to_constant();
      return l == val;
    });
  return i != set.end();
}

std::string expr_to_str(const exprt &expr)
{
  auto st = symbol_tablet{};
  auto ns = namespacet{st};
  auto expr_str = std::string{};

  auto lang = new_ansi_c_language();
  lang->from_expr(expr, expr_str, ns);

  return expr_str;
}

template <class Container, typename UnaryOp>
std::string container_to_str(const Container &con, UnaryOp unaryOp)
{
  auto as_str = std::vector<std::string>{};
  std::transform(con.begin(), con.end(), std::back_inserter(as_str), unaryOp);
  auto out = std::ostringstream{};
  out << "{ ";
  join_strings(out, as_str.begin(), as_str.end(), ", ");
  out << " }";
  return out.str();
}

std::string set_to_str(const abstract_object_sett &set)
{
  return container_to_str(set, [](const abstract_object_pointert &lhs) {
    return expr_to_str(lhs->to_constant());
  });
}

std::string exprs_to_str(const std::vector<exprt> &values)
{
  return container_to_str(
    values, [](const exprt &lhs) { return expr_to_str(lhs); });
}

void EXPECT(
  std::shared_ptr<const constant_abstract_valuet> &result,
  exprt expected_value)
{
  REQUIRE(result);

  REQUIRE_FALSE(result->is_top());
  REQUIRE_FALSE(result->is_bottom());

  auto result_expr = result->to_constant();
  INFO(
    "Expect " + expr_to_str(result_expr) + " to equal " +
    expr_to_str(expected_value));
  REQUIRE(result_expr == expected_value);
}

void EXPECT(
  std::shared_ptr<const value_set_abstract_objectt> &result,
  const std::vector<exprt> &expected_values)
{
  REQUIRE(result);

  REQUIRE_FALSE(result->is_top());
  REQUIRE_FALSE(result->is_bottom());

  auto values = result->get_values();
  REQUIRE(values.size() == expected_values.size());

  auto value_string = set_to_str(values);
  auto expected_string = exprs_to_str(expected_values);

  for(auto &ev : expected_values)
  {
    INFO("Expect " + value_string + " to include " + expected_string);
    REQUIRE(set_contains(values, ev));
  }
}

void EXPECT_UNMODIFIED(
  std::shared_ptr<const abstract_objectt> &result,
  bool modified)
{
  CHECK_FALSE(modified);
}

void EXPECT_UNMODIFIED(
  std::shared_ptr<const constant_abstract_valuet> &result,
  bool modified,
  exprt expected_value)
{
  CHECK_FALSE(modified);
  EXPECT(result, expected_value);
}

void EXPECT_UNMODIFIED(
  std::shared_ptr<const value_set_abstract_objectt> &result,
  bool modified,
  const std::vector<exprt> &expected_values)
{
  CHECK_FALSE(modified);
  EXPECT(result, expected_values);
}

void EXPECT_TOP(std::shared_ptr<const abstract_objectt> result)
{
  REQUIRE(result);

  REQUIRE(result->is_top());
  REQUIRE_FALSE(result->is_bottom());
}

void EXPECT_TOP(std::shared_ptr<const value_set_abstract_objectt> &result)
{
  REQUIRE(result);

  REQUIRE(result->is_top());
  REQUIRE_FALSE(result->is_bottom());

  auto values = result->get_values();
  REQUIRE(values.size() == 1);
  REQUIRE(values.first()->is_top());
  REQUIRE_FALSE(values.first()->is_bottom());
}

void EXPECT_BOTTOM(std::shared_ptr<const abstract_objectt> result)
{
  REQUIRE(result);

  REQUIRE_FALSE(result->is_top());
  REQUIRE(result->is_bottom());
}

static std::shared_ptr<const abstract_objectt> add(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2,
  abstract_environmentt &environment,
  namespacet &ns)
{
  auto op1_sym = symbol_exprt("op1", op1->type());
  auto op2_sym = symbol_exprt("op2", op2->type());
  environment.assign(op1_sym, op1, ns);
  environment.assign(op2_sym, op2, ns);

  auto result = environment.eval(plus_exprt(op1_sym, op2_sym), ns);

  return result;
}

std::shared_ptr<const constant_abstract_valuet> add_as_constant(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2,
  abstract_environmentt &environment,
  namespacet &ns)
{
  auto result = add(op1, op2, environment, ns);
  auto cv = as_constant(result);

  INFO("Result should be a constant")
  REQUIRE(cv);
  return cv;
}

std::shared_ptr<const value_set_abstract_objectt> add_as_value_set(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2,
  abstract_environmentt &environment,
  namespacet &ns)
{
  auto result = add(op1, op2, environment, ns);
  auto vs = as_value_set(result);

  INFO("Result should be a value set")
  REQUIRE(vs);
  return vs;
}

std::shared_ptr<const value_set_abstract_objectt> add_as_value_set(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2,
  const abstract_object_pointert &op3,
  abstract_environmentt &environment,
  namespacet &ns)
{
  auto op1_sym = symbol_exprt("op1", op1->type());
  auto op2_sym = symbol_exprt("op2", op2->type());
  auto op3_sym = symbol_exprt("op3", op3->type());
  environment.assign(op1_sym, op1, ns);
  environment.assign(op2_sym, op2, ns);
  environment.assign(op3_sym, op3, ns);

  auto result =
    environment.eval(plus_exprt(plus_exprt(op1_sym, op2_sym), op3_sym), ns);

  auto vs = as_value_set(result);

  INFO("Result should be a value set")
  REQUIRE(vs);
  return vs;
}
