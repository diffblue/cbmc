/*******************************************************************\

 Module: Unit tests helpers for abstract objects

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include "variable_sensitivity_test_helpers.h"

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/interval_abstract_value.h>
#include <analyses/variable-sensitivity/value_set_abstract_object.h>
#include <analyses/variable-sensitivity/variable_sensitivity_domain.h>

#include <ansi-c/ansi_c_language.h>

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>
#include <util/string_utils.h>
#include <util/symbol_table.h>

std::shared_ptr<const constant_abstract_valuet>
make_constant(exprt val, abstract_environmentt &env, namespacet &ns)
{
  return std::make_shared<constant_abstract_valuet>(val, env, ns);
}

std::shared_ptr<const constant_abstract_valuet> make_top_constant()
{
  return std::make_shared<constant_abstract_valuet>(
    integer_typet(), true, false);
}

std::shared_ptr<const constant_abstract_valuet> make_bottom_constant()
{
  return std::make_shared<constant_abstract_valuet>(
    integer_typet(), false, true);
}

std::shared_ptr<const interval_abstract_valuet> make_interval(
  const exprt &vall,
  const exprt &valh,
  abstract_environmentt &env,
  namespacet &ns)
{
  auto interval = constant_interval_exprt(vall, valh);
  return make_interval(interval, env, ns);
}

std::shared_ptr<const interval_abstract_valuet> make_interval(
  const binary_relation_exprt &val,
  abstract_environmentt &env,
  namespacet &ns)
{
  return std::make_shared<interval_abstract_valuet>(val, env, ns);
}
std::shared_ptr<const interval_abstract_valuet> make_interval(
  const constant_interval_exprt &val,
  abstract_environmentt &env,
  namespacet &ns)
{
  return std::make_shared<interval_abstract_valuet>(val, env, ns);
}

std::shared_ptr<const interval_abstract_valuet> make_top_interval()
{
  return std::make_shared<interval_abstract_valuet>(
    signedbv_typet(32), true, false);
}

std::shared_ptr<const interval_abstract_valuet> make_bottom_interval()
{
  return std::make_shared<interval_abstract_valuet>(
    signedbv_typet(32), false, true);
}

std::shared_ptr<const value_set_abstract_objectt>
make_value_set(exprt val, abstract_environmentt &env, namespacet &ns)
{
  auto vals = std::vector<exprt>{val};
  return make_value_set(vals, env, ns);
}

std::shared_ptr<const value_set_abstract_objectt> make_value_set(
  const std::vector<exprt> &vals,
  abstract_environmentt &env,
  namespacet &ns)
{
  auto initial_values = abstract_object_sett{};
  for(auto v : vals)
  {
    if(v.id() == ID_constant_interval)
      initial_values.insert(
        std::make_shared<interval_abstract_valuet>(v, env, ns));
    else
      initial_values.insert(make_constant(v, env, ns));
  }

  auto vs = value_set_abstract_objectt::make_value_set(initial_values);
  return std::dynamic_pointer_cast<const value_set_abstract_objectt>(vs);
}

std::shared_ptr<const value_set_abstract_objectt> make_bottom_value_set()
{
  return std::make_shared<const value_set_abstract_objectt>(
    integer_typet(), false, true);
}

std::shared_ptr<const value_set_abstract_objectt> make_top_value_set()
{
  return std::make_shared<const value_set_abstract_objectt>(integer_typet());
}

abstract_object_pointert make_bottom_object()
{
  return std::make_shared<abstract_objectt>(integer_typet(), false, true);
}

abstract_object_pointert make_top_object()
{
  return std::make_shared<abstract_objectt>(integer_typet(), true, false);
}

std::shared_ptr<const constant_abstract_valuet>
as_constant(const abstract_object_pointert &aop)
{
  return std::dynamic_pointer_cast<const constant_abstract_valuet>(aop);
}

std::shared_ptr<const interval_abstract_valuet>
as_interval(const abstract_object_pointert &aop)
{
  return std::dynamic_pointer_cast<const interval_abstract_valuet>(aop);
}

std::shared_ptr<const value_set_abstract_objectt>
as_value_set(const abstract_object_pointert &aop)
{
  return std::dynamic_pointer_cast<const value_set_abstract_objectt>(
    aop->unwrap_context());
}

bool set_contains(const std::vector<exprt> &set, const exprt &val)
{
  auto i = std::find_if(
    set.begin(), set.end(), [&val](const exprt &lhs) { return lhs == val; });
  return i != set.end();
}

bool set_contains(const abstract_object_sett &set, const exprt &val)
{
  auto i = std::find_if(
    set.begin(), set.end(), [&val](const abstract_object_pointert &lhs) {
      auto l = lhs->to_constant();
      auto interval =
        std::dynamic_pointer_cast<const interval_abstract_valuet>(lhs);
      if(interval)
        l = interval->to_interval();
      return l == val;
    });
  return i != set.end();
}

static std::string interval_to_str(const constant_interval_exprt &expr);

exprt to_expr(int v)
{
  return from_integer(v, integer_typet());
}

std::string expr_to_str(const exprt &expr)
{
  if(expr.id() == ID_constant_interval)
    return interval_to_str(to_constant_interval_expr(expr));
  if(expr.id() == ID_max)
    return "max";
  if(expr.id() == ID_min)
    return "min";

  auto st = symbol_tablet{};
  auto ns = namespacet{st};
  auto expr_str = std::string{};

  auto lang = new_ansi_c_language();
  lang->from_expr(expr, expr_str, ns);

  return expr_str;
}

static std::string interval_to_str(const constant_interval_exprt &expr)
{
  auto lower = expr_to_str(expr.get_lower());
  auto upper = expr_to_str(expr.get_upper());
  return "[" + lower + "," + upper + "]";
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
    auto i = std::dynamic_pointer_cast<const interval_abstract_valuet>(lhs);
    return i ? interval_to_str(i->to_interval())
             : expr_to_str(lhs->to_constant());
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
  std::shared_ptr<const interval_abstract_valuet> &result,
  exprt lower_value,
  exprt upper_value)
{
  REQUIRE(result);

  REQUIRE_FALSE(result->is_top());
  REQUIRE_FALSE(result->is_bottom());

  auto expected_interval = constant_interval_exprt(lower_value, upper_value);
  auto result_expr = result->to_interval();
  REQUIRE(result_expr == expected_interval);
}

void EXPECT(
  std::shared_ptr<const value_set_abstract_objectt> &result,
  const std::vector<exprt> &expected_values)
{
  REQUIRE(result);

  REQUIRE_FALSE(result->is_top());
  REQUIRE_FALSE(result->is_bottom());

  auto values = result->get_values();
  auto value_string = set_to_str(values);
  auto expected_string = exprs_to_str(expected_values);

  INFO("Expect " + value_string + " to match " + expected_string);
  REQUIRE(values.size() == expected_values.size());

  for(auto &ev : expected_values)
    REQUIRE(set_contains(values, ev));
}

void EXPECT(
  const std::vector<exprt> &values,
  const std::vector<exprt> &expected_values)
{
  auto value_string = exprs_to_str(values);
  auto expected_string = exprs_to_str(expected_values);
  INFO("Expect " + value_string + " to match " + expected_string);
  REQUIRE(values.size() == expected_values.size());

  for(auto &ev : expected_values)
  {
    INFO("Expect " + value_string + " to match " + expected_string);
    REQUIRE(set_contains(values, ev));
  }
}

void EXPECT_INDEX(
  std::shared_ptr<const abstract_objectt> &result,
  int index,
  int expected,
  abstract_environmentt &environment,
  namespacet &ns)
{
  auto type = signedbv_typet(32);
  auto index_expr = index_exprt(
    exprt(ID_nil, array_typet(typet(), nil_exprt())),
    from_integer(index, type));
  auto expr = result->expression_transform(index_expr, {}, environment, ns)
                ->to_constant();

  auto expected_expr = from_integer(expected, type);
  INFO(
    "Expect array[" + std::to_string(index) +
    "] == " + std::to_string(expected));
  REQUIRE(expr_to_str(expr) == expr_to_str(expected_expr));
}

void EXPECT_INDEX(
  std::shared_ptr<const abstract_objectt> &result,
  int index,
  std::vector<int> expected,
  abstract_environmentt &environment,
  namespacet &ns)
{
  auto type = signedbv_typet(32);
  auto index_expr = index_exprt(
    exprt(ID_nil, array_typet(typet(), nil_exprt())),
    from_integer(index, type));
  auto value =
    as_value_set(result->expression_transform(index_expr, {}, environment, ns));

  auto expected_exprs = std::vector<exprt>{};
  for(int e : expected)
    expected_exprs.push_back(from_integer(e, type));
  INFO(
    "Expect array[" + std::to_string(index) +
    "] == " + exprs_to_str(expected_exprs));
  EXPECT(value, expected_exprs);
}

void EXPECT_INDEX_TOP(
  std::shared_ptr<const abstract_objectt> &result,
  int index,
  abstract_environmentt &environment,
  namespacet &ns)
{
  auto type = signedbv_typet(32);
  auto index_expr = index_exprt(
    exprt(ID_nil, array_typet(typet(), nil_exprt())),
    from_integer(index, type));
  auto value = result->expression_transform(index_expr, {}, environment, ns);

  INFO("Expect array[" + std::to_string(index) + "] to be TOP");
  REQUIRE(value->is_top());
}

void EXPECT_UNMODIFIED(
  std::shared_ptr<const abstract_objectt> &result,
  bool modified)
{
  CHECK_FALSE(modified);
}

void EXPECT_MODIFIED(
  std::shared_ptr<const abstract_objectt> &result,
  bool modified)
{
  CHECK(modified);
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
  merge_result<const constant_abstract_valuet> &result,
  exprt expected_value)
{
  EXPECT_UNMODIFIED(result.result, result.modified, expected_value);
}

void EXPECT_UNMODIFIED(
  std::shared_ptr<const interval_abstract_valuet> &result,
  bool modified,
  exprt lower_value,
  exprt upper_value)
{
  CHECK_FALSE(modified);
  EXPECT(result, lower_value, upper_value);
}

void EXPECT_UNMODIFIED(
  merge_result<const interval_abstract_valuet> &result,
  exprt lower_value,
  exprt upper_value)
{
  EXPECT_UNMODIFIED(result.result, result.modified, lower_value, upper_value);
}

void EXPECT_UNMODIFIED(
  std::shared_ptr<const value_set_abstract_objectt> &result,
  bool modified,
  const std::vector<exprt> &expected_values)
{
  CHECK_FALSE(modified);
  EXPECT(result, expected_values);
}

void EXPECT_UNMODIFIED(
  merge_result<const value_set_abstract_objectt> &result,
  const std::vector<exprt> &expected_values)
{
  EXPECT_UNMODIFIED(result.result, result.modified, expected_values);
}

void EXPECT_MODIFIED(
  std::shared_ptr<const constant_abstract_valuet> &result,
  bool modified,
  exprt expected_value)
{
  CHECK(modified);
  EXPECT(result, expected_value);
}

void EXPECT_MODIFIED(
  merge_result<const constant_abstract_valuet> &result,
  exprt expected_value)
{
  EXPECT_MODIFIED(result.result, result.modified, expected_value);
}

void EXPECT_MODIFIED(
  std::shared_ptr<const interval_abstract_valuet> &result,
  bool modified,
  exprt lower_value,
  exprt upper_value)
{
  CHECK(modified);
  EXPECT(result, lower_value, upper_value);
}

void EXPECT_MODIFIED(
  merge_result<const interval_abstract_valuet> &result,
  exprt lower_value,
  exprt upper_value)
{
  EXPECT_MODIFIED(result.result, result.modified, lower_value, upper_value);
}

void EXPECT_MODIFIED(
  std::shared_ptr<const value_set_abstract_objectt> &result,
  bool modified,
  const std::vector<exprt> &expected_values)
{
  CHECK(modified);
  EXPECT(result, expected_values);
}

void EXPECT_MODIFIED(
  merge_result<const value_set_abstract_objectt> &result,
  const std::vector<exprt> &expected_values)
{
  EXPECT_MODIFIED(result.result, result.modified, expected_values);
}

void EXPECT_TOP(std::shared_ptr<const abstract_objectt> result)
{
  REQUIRE(result);

  REQUIRE(result->is_top());
  REQUIRE_FALSE(result->is_bottom());
}

void EXPECT_TOP(abstract_objectt::combine_result const &result)
{
  EXPECT_TOP(result.object);
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

void EXPECT_BOTTOM(abstract_objectt::combine_result const &result)
{
  EXPECT_BOTTOM(result.object);
}

std::shared_ptr<const abstract_objectt> add(
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

std::shared_ptr<const interval_abstract_valuet> add_as_interval(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2,
  abstract_environmentt &environment,
  namespacet &ns)
{
  auto result = add(op1, op2, environment, ns);
  auto i = as_interval(result);

  INFO("Result should be an interval")
  REQUIRE(i);
  return i;
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

void THEN_PREDICATE(const abstract_object_pointert &obj, const std::string &out)
{
  const auto x_name = symbol_exprt(dstringt("x"), obj->type());
  auto pred = obj->to_predicate(x_name);
  THEN("predicate is " + out)
  {
    auto repr = expr_to_str(pred);
    REQUIRE(repr == out);
  }
}

void THEN_PREDICATE(const exprt &pred, const std::string &out)
{
  THEN("predicate is " + out)
  {
    auto repr = expr_to_str(pred);
    REQUIRE(repr == out);
  }
}

void THEN_PREDICATE(const abstract_environmentt &env, const std::string &out)
{
  THEN_PREDICATE(env.to_predicate(), out);
}

void THEN_PREDICATE(
  const variable_sensitivity_domaint &domain,
  const std::string &out)
{
  THEN_PREDICATE(domain.to_predicate(), out);
}
