/*******************************************************************\

 Module: Array Access Unit Tests

 Author: Jez Higgins

\*******************************************************************/
#include <testing-utils/use_catch.h>

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/full_array_abstract_object.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <util/arith_tools.h>
#include <util/mathematical_types.h>

void test_array(
  std::vector<int> contents,
  abstract_environmentt &environment,
  namespacet &ns);

const auto TOP = -99;

SCENARIO(
  "eval-member-access",
  "[core][analyses][variable-sensitivity][eval-member-access]")
{
  auto environment =
    abstract_environmentt{variable_sensitivity_object_factoryt::configured_with(
      vsd_configt::constant_domain())};
  environment.make_top(); // Domains are bottom on construction

  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  GIVEN("An array of {1, 2, 3}")
  {
    test_array({1, 2, 3}, environment, ns);
  }
  GIVEN("An array of {1, 2, TOP}")
  {
    test_array({1, 2, TOP}, environment, ns);
  }
  GIVEN("An array of {TOP, 2, TOP}")
  {
    test_array({TOP, 2, TOP}, environment, ns);
  }
}

exprt make_array(
  std::vector<int> contents,
  abstract_environmentt &environment,
  namespacet &ns);

exprt fetch_element(
  int index,
  exprt &array,
  abstract_environmentt &environment,
  namespacet &ns);

exprt integer_expression(int i);
exprt top_expression();

void test_array(
  std::vector<int> values,
  abstract_environmentt &environment,
  namespacet &ns)
{
  auto array = make_array(values, environment, ns);

  WHEN("getting index 0")
  {
    auto result_expr = fetch_element(0, array, environment, ns);

    THEN("we get the first element")
    {
      auto result_str = result_expr.pretty();
      REQUIRE(result_expr == integer_expression(values[0]));
    }
  }
  WHEN("getting index 2")
  {
    auto result_expr = fetch_element(2, array, environment, ns);

    THEN("we get the third element")
    {
      auto result_str = result_expr.pretty();
      REQUIRE(result_expr == integer_expression(values[2]));
    }
  }
  WHEN("getting index 5")
  {
    auto result_expr = fetch_element(5, array, environment, ns);

    THEN("we get a nil element")
    {
      auto result_str = result_expr.pretty();
      REQUIRE(result_expr == nil_exprt());
    }
  }
}

exprt fetch_element(
  int index,
  exprt &array,
  abstract_environmentt &environment,
  namespacet &ns)
{
  auto index_expression =
    index_exprt(array, from_integer(index, integer_typet()));
  auto element = environment.eval(index_expression, ns);

  auto object =
    std::dynamic_pointer_cast<const context_abstract_objectt>(element);
  REQUIRE(object);

  if(object->is_top()) // oh!
    return object->to_constant();

  auto value =
    std::dynamic_pointer_cast<const abstract_objectt>(object->unwrap_context());
  REQUIRE(value);
  return value->to_constant();
}

exprt make_array(
  std::vector<int> contents,
  abstract_environmentt &environment,
  namespacet &ns)
{
  const array_typet array_type(
    integer_typet(), from_integer(contents.size(), integer_typet()));

  exprt::operandst array_elements;
  for(auto v : contents)
  {
    array_elements.push_back(integer_expression(v));
  }

  auto populate_array = array_exprt(array_elements, array_type);
  auto array_value = std::make_shared<full_array_abstract_objectt>(
    populate_array, environment, ns);
  REQUIRE_FALSE(array_value->is_top());
  REQUIRE_FALSE(array_value->is_bottom());

  auto array = symbolt();
  array.name = array.base_name = array.pretty_name = "array";
  array.type = array_type;

  environment.assign(array.symbol_expr(), array_value, ns);

  return array.symbol_expr();
}

exprt integer_expression(int i)
{
  return (i == TOP) ? top_expression() : from_integer(i, integer_typet());
}

exprt top_expression()
{
  auto top_value =
    std::make_shared<abstract_objectt>(integer_typet(), true, false);
  return top_value->to_constant();
}
