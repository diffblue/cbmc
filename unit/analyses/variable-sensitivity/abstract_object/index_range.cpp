#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/value_set_abstract_object.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <testing-utils/use_catch.h>
#include <util/arith_tools.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

SCENARIO(
  "index_range for constant_abstract_values"
  "[core][analyses][variable-sensitivity][constant_abstract_value][index-"
  "range]")
{
  auto type = signedbv_typet(32);
  auto object_factory = variable_sensitivity_object_factoryt::configured_with(
    vsd_configt::constant_domain());
  abstract_environmentt env{object_factory};
  env.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  GIVEN("an integer constant has an index_range")
  {
    auto int_value = 99;
    auto value_expr = from_integer(int_value, type);
    auto value =
      std::make_shared<constant_abstract_valuet>(value_expr, env, ns);

    auto range = value->index_range(ns);

    THEN("range should have a value")
    {
      REQUIRE(range->advance_to_next() == true);

      mp_integer index;
      to_integer(to_constant_expr(range->current()), index);
      REQUIRE(index == int_value);

      REQUIRE(range->advance_to_next() == false);
    }
  }

  GIVEN("a top constant's range is has a single nil expression")
  {
    auto value = std::make_shared<constant_abstract_valuet>(type);

    auto range = value->index_range(ns);

    THEN("range should have a nil expr")
    {
      REQUIRE(range->advance_to_next() == true);

      REQUIRE(range->current() == nil_exprt());

      REQUIRE(range->advance_to_next() == false);
    }
  }
}

SCENARIO(
  "index_range for interval_abstract_values"
  "[core][analyses][variable-sensitivity][interval_abstract_value][index-"
  "range]")
{
  auto object_factory = variable_sensitivity_object_factoryt::configured_with(
    vsd_configt::intervals());
  abstract_environmentt env{object_factory};
  env.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  auto type = signedbv_typet(32);

  GIVEN("a top intervals's range is empty")
  {
    auto value = std::make_shared<interval_abstract_valuet>(type, true, false);

    auto range = value->index_range(ns);

    THEN("range should be empty")
    {
      REQUIRE(range->advance_to_next() == false);
    }
  }

  GIVEN("a single-value interval's index_range has a single element")
  {
    auto int_value = 99;
    auto value_expr = from_integer(int_value, type);
    auto value =
      std::make_shared<interval_abstract_valuet>(value_expr, env, ns);

    auto range = value->index_range(ns);

    THEN("range should have a single value")
    {
      REQUIRE(range->advance_to_next() == true);

      mp_integer index;
      to_integer(to_constant_expr(range->current()), index);
      REQUIRE(index == int_value);

      REQUIRE(range->advance_to_next() == false);
    }
  }

  GIVEN("a [99,100] interval's index_range has two elements")
  {
    auto int_value = 99;
    auto value_expr = from_integer(int_value, type);
    auto value = std::make_shared<interval_abstract_valuet>(
      constant_interval_exprt(
        from_integer(int_value, type), from_integer(int_value + 1, type), type),
      env,
      ns);

    auto range = value->index_range(ns);

    THEN("range should have two values")
    {
      REQUIRE(range->advance_to_next() == true);

      mp_integer index;
      to_integer(to_constant_expr(range->current()), index);
      REQUIRE(index == int_value);

      REQUIRE(range->advance_to_next() == true);

      to_integer(to_constant_expr(range->current()), index);
      REQUIRE(index == int_value + 1);

      REQUIRE(range->advance_to_next() == false);
    }
  }

  GIVEN("a [99,102] interval's index_range has four elements")
  {
    auto int_value = 99;
    auto value_expr = from_integer(int_value, type);
    auto value = std::make_shared<interval_abstract_valuet>(
      constant_interval_exprt(
        from_integer(int_value, type), from_integer(int_value + 3, type), type),
      env,
      ns);

    auto range = value->index_range(ns);

    THEN("range should have four values")
    {
      for(int i = 0; i != 4; ++i)
      {
        REQUIRE(range->advance_to_next() == true);

        mp_integer index;
        to_integer(to_constant_expr(range->current()), index);
        REQUIRE(index == int_value + i);
      }

      REQUIRE(range->advance_to_next() == false);
    }
  }
}

SCENARIO(
  "index_range for value_set_abstract_values"
  "[core][analyses][variable-sensitivity][value_set_abstract_value][index-"
  "range]")
{
  auto object_factory = variable_sensitivity_object_factoryt::configured_with(
    vsd_configt::intervals());
  abstract_environmentt env{object_factory};
  env.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  auto type = signedbv_typet(32);

  GIVEN("a value_set is empty")
  {
    auto value =
      std::make_shared<value_set_abstract_objectt>(type, true, false);
    auto range = value->index_range(ns);

    THEN("range should have a nil expr")
    {
      REQUIRE(range->advance_to_next() == true);

      REQUIRE(range->current() == nil_exprt());

      REQUIRE(range->advance_to_next() == false);
    }
  }
}
