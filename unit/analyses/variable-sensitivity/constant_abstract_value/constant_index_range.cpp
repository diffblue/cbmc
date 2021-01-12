#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <testing-utils/use_catch.h>
#include <util/namespace.h>
#include <util/symbol_table.h>
#include <util/arith_tools.h>
#include <util/mathematical_types.h>

SCENARIO(
  "the index_range for a constant has a single value"
  "[core][analyses][variable-sensitivity][constant-abstract-value][index-range]")
{
  auto object_factory = variable_sensitivity_object_factoryt::configured_with(
    vsd_configt::constant_domain());
  abstract_environmentt env { object_factory };
  env.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("an constant index_range")
  {
    auto int_value = 99;
    auto value_expr = from_integer(int_value, integer_typet());
    auto value = std::make_shared<constant_abstract_valuet>(value_expr, env, ns);

    auto range = value->index_range();

    THEN("range should have a value")
    {
      REQUIRE(range->advance_to_next() == true);

      mp_integer index;
      to_integer(to_constant_expr(range->current()), index);
      REQUIRE(index == int_value);

      REQUIRE(range->advance_to_next() == false);
    }
  }

  GIVEN("a top constant")
  {
    auto value = std::make_shared<constant_abstract_valuet>(integer_typet());

    auto range = value->index_range();

    THEN("range should be empty")
    {
      REQUIRE(range->advance_to_next() == false);
    }
  }
}
