/*******************************************************************\

 Module: Unit tests for variable/sensitivity/abstract_object::index_range

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include "analyses/variable-sensitivity/variable_sensitivity_test_helpers.h"
#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/constant_abstract_value.h>
#include <analyses/variable-sensitivity/value_set_abstract_object.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>

SCENARIO(
  "index_range for constant_abstract_values"
  "[core][analyses][variable-sensitivity][constant_abstract_value][index_"
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
    auto value = make_constant(value_expr, env, ns);

    auto range = value->index_range(ns);

    THEN("range should have a value")
    {
      auto i = range.begin();
      REQUIRE(i != range.end());

      mp_integer index;
      to_integer(to_constant_expr(*i), index);
      REQUIRE(index == int_value);

      ++i;
      REQUIRE(i == range.end());
    }
    THEN("iterator has a single value")
    {
      auto i = range.begin();
      REQUIRE(i != range.end());

      mp_integer index;
      to_integer(to_constant_expr(*i), index);
      REQUIRE(index == int_value);

      ++i;
      REQUIRE(i == range.end());
    }
  }

  GIVEN("a top constant's range is has a single nil expression")
  {
    auto value = make_top_constant();

    auto range = value->index_range(ns);

    THEN("range should have a nil expr")
    {
      auto i = range.begin();
      REQUIRE(i != range.end());

      REQUIRE(*i == nil_exprt());
      ++i;

      REQUIRE(i == range.end());
    }
  }
}

SCENARIO(
  "index_range for interval_abstract_values"
  "[core][analyses][variable-sensitivity][interval_abstract_value][index_"
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
    auto value = make_top_interval();

    auto range = value->index_range(ns);

    THEN("range should be empty")
    {
      REQUIRE(range.begin() == range.end());
    }
  }

  GIVEN("a single-value interval's index_range has a single element")
  {
    auto int_value = 99;
    auto value_expr = from_integer(int_value, type);
    auto value = make_interval(value_expr, value_expr, env, ns);

    auto range = value->index_range(ns);

    THEN("range should have a single value")
    {
      auto i = range.begin();
      REQUIRE(i != range.end());

      mp_integer index;
      to_integer(to_constant_expr(*i), index);
      REQUIRE(index == int_value);
      ++i;

      REQUIRE(i == range.end());
    }
  }

  GIVEN("a [99,100] interval's index_range has two elements")
  {
    auto int_value = 99;
    auto lower = from_integer(int_value, type);
    auto upper = from_integer(int_value + 1, type);
    auto value = make_interval(lower, upper, env, ns);

    auto range = value->index_range(ns);

    THEN("range should have two values")
    {
      auto i = range.begin();
      REQUIRE(i != range.end());

      mp_integer index;
      to_integer(to_constant_expr(*i), index);
      REQUIRE(index == int_value);
      ++i;

      REQUIRE(i != range.end());

      to_integer(to_constant_expr(*i), index);
      REQUIRE(index == int_value + 1);
      ++i;

      REQUIRE(i == range.end());
    }
  }

  GIVEN("a [99,102] interval's index_range has four elements")
  {
    auto int_value = 99;
    auto lower = from_integer(int_value, type);
    auto upper = from_integer(int_value + 3, type);
    auto value = make_interval(lower, upper, env, ns);

    auto range = value->index_range(ns);

    THEN("range has four values")
    {
      int i = 0;
      for(const auto &e : range)
      {
        mp_integer index;
        to_integer(to_constant_expr(e), index);
        REQUIRE(index == int_value + i);
        ++i;
      }

      REQUIRE(i == 4);
    }
  }
}

SCENARIO(
  "index_range for value_set_abstract_values"
  "[core][analyses][variable-sensitivity][value_set_abstract_value][index_"
  "range]")
{
  auto object_factory = variable_sensitivity_object_factoryt::configured_with(
    vsd_configt::intervals());
  abstract_environmentt env{object_factory};
  env.make_top();
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  auto type = signedbv_typet(32);

  GIVEN("a TOP value_set is empty")
  {
    auto value = make_top_value_set();
    auto range = value->index_range(ns);

    THEN("range should have a nil expr")
    {
      auto i = range.begin();
      REQUIRE(i != range.end());

      REQUIRE(*i == nil_exprt());
      ++i;

      REQUIRE(i == range.end());
    }
  }
  GIVEN("a value_set { 99, 100, 101, 102 } index_range has four elements")
  {
    auto int_value = 99;
    auto _99 = from_integer(int_value, type);
    auto _100 = from_integer(100, type);
    auto _101 = from_integer(101, type);
    auto _102 = from_integer(102, type);
    auto value = make_value_set({_99, _100, _101, _102}, env, ns);

    auto range = value->index_range(ns);

    THEN("range has four values")
    {
      auto values = std::vector<exprt>();
      for(const auto &e : range)
        values.push_back(to_constant_expr(e));

      REQUIRE(values.size() == 4);
      EXPECT(values, {_99, _100, _101, _102});
    }
  }
  GIVEN("a value_set { [99, 102] } index_range has four elements")
  {
    auto int_value = 99;
    auto _99 = from_integer(int_value, type);
    auto _100 = from_integer(100, type);
    auto _101 = from_integer(101, type);
    auto _102 = from_integer(102, type);
    auto _99_102 = constant_interval_exprt(_99, _102);
    auto value = make_value_set({_99_102}, env, ns);

    auto range = value->index_range(ns);

    THEN("range has four values")
    {
      auto values = std::vector<exprt>();
      for(const auto &e : range)
        values.push_back(to_constant_expr(e));

      REQUIRE(values.size() == 4);
      EXPECT(values, {_99, _100, _101, _102});
    }
  }
  GIVEN("a value_set { 99, 100, [101, 102] } index_range has four elements")
  {
    auto int_value = 99;
    auto _99 = from_integer(int_value, type);
    auto _100 = from_integer(100, type);
    auto _101 = from_integer(101, type);
    auto _102 = from_integer(102, type);
    auto _101_102 = constant_interval_exprt(_101, _102);
    auto value = make_value_set({_99, _101_102, _100}, env, ns);

    auto range = value->index_range(ns);

    THEN("range has four values")
    {
      auto values = std::vector<exprt>();
      for(const auto &e : range)
        values.push_back(to_constant_expr(e));

      REQUIRE(values.size() == 4);
      EXPECT(values, {_99, _100, _101, _102});
    }
  }
  GIVEN("a value_set { [99, 102], 100, 101 } index_range has four elements")
  {
    auto int_value = 99;
    auto _99 = from_integer(int_value, type);
    auto _100 = from_integer(100, type);
    auto _101 = from_integer(101, type);
    auto _102 = from_integer(102, type);
    auto _99_102 = constant_interval_exprt(_99, _102);
    auto value = make_value_set({_99_102, _100, _101}, env, ns);

    auto range = value->index_range(ns);

    THEN("range has four values")
    {
      auto values = std::vector<exprt>();
      for(const auto &e : range)
        values.push_back(to_constant_expr(e));

      REQUIRE(values.size() == 4);
      EXPECT(values, {_99, _100, _101, _102});
    }
  }
}
