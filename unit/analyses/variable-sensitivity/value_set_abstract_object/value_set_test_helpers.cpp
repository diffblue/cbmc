/*******************************************************************\

 Module: Unit tests helpers for value_set_abstract_objects

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include "value_set_test_helpers.h"
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
  std::shared_ptr<const value_set_abstract_objectt> &result,
  const std::vector<exprt> &expected_values)
{
  REQUIRE(result);

  // Correctness of merge
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
  std::shared_ptr<const value_set_abstract_objectt> &result,
  bool modified,
  const std::vector<exprt> &expected_values)
{
  CHECK_FALSE(modified);
  EXPECT(result, expected_values);
}

void EXPECT_TOP(std::shared_ptr<const value_set_abstract_objectt> &result)
{
  REQUIRE(result);

  REQUIRE(result->is_top());
  REQUIRE_FALSE(result->is_bottom());

  auto values = result->get_values();
  REQUIRE(values.empty());
}
