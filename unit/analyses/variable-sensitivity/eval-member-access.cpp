#include <testing-utils/use_catch.h>

#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/constant_array_abstract_object.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <util/arith_tools.h>
#include <util/mathematical_types.h>

exprt make_array(
  std::vector<int> contents,
  abstract_environmentt &environment,
  namespacet &ns
);

exprt fetch_element(
  int index,
  exprt &array,
  abstract_environmentt &environment,
  namespacet &ns
);

SCENARIO(
  "eval-member-access",
  "[core][analyses][variable-sensitivity][eval-member-access]")
{
  auto environment = abstract_environmentt {
    variable_sensitivity_object_factoryt::configured_with(vsd_configt::constant_domain())
  };
  environment.make_top(); // Domains are bottom on construction

  symbol_tablet symbol_table;
  namespacet ns { symbol_table };

  GIVEN("An array of size 3")
  {
    auto values = std::vector<int>{ 1, 2, 3 };
    auto array = make_array(values, environment, ns);

    WHEN("getting index 0") {
      auto result_expr = fetch_element(0, array, environment, ns);

      THEN("we get the first element") {
        REQUIRE(result_expr == from_integer(values[0], integer_typet()));
      }
    }
    WHEN("getting index 2") {
      auto  result_expr = fetch_element(2, array, environment, ns);

      THEN("we get the third element") {
        REQUIRE(result_expr == from_integer(values[2], integer_typet()));
      }
    }
    WHEN("getting index 5") {
      auto result_value = fetch_element(5, array, environment, ns);

      THEN("we get a nil element") {
        REQUIRE(result_value == nil_exprt());
      }
    }
  }
}

exprt fetch_element(
  int index,
  exprt &array,
  abstract_environmentt &environment,
  namespacet &ns
) {
  auto index_expression = index_exprt(array, from_integer(index, integer_typet()));
  auto first_element = environment.eval(index_expression, ns);

  REQUIRE(std::dynamic_pointer_cast<const context_abstract_objectt>(first_element));
  const auto unwrapped =
    std::dynamic_pointer_cast<const context_abstract_objectt>(first_element)
        ->unwrap_context();
  auto value = std::dynamic_pointer_cast<const abstract_valuet>(unwrapped);
  REQUIRE(value);
  return value->to_constant();
}

exprt make_array(
  std::vector<int> contents,
  abstract_environmentt &environment,
  namespacet &ns
) {
  const array_typet array_type(
    integer_typet(),
    from_integer(contents.size(), integer_typet())
  );

  // int val1[3] = {1, 2, 3}
  exprt::operandst array_elements;
  for (auto v : contents) {
    array_elements.push_back(
      from_integer(v, integer_typet())
    );
  }

  auto populate_array = array_exprt(array_elements, array_type);
  auto array_value = std::make_shared<constant_array_abstract_objectt>(
    populate_array, environment, ns);

  auto array = symbolt();
  array.name = array.base_name = array.pretty_name = "array";
  array.type = array_type;

  environment.assign(array.symbol_expr(), array_value, ns);

  return array.symbol_expr();
}
