/*******************************************************************\

 Module: Unit tests for value_set_abstract_valuet compacting

 Compacting occurs when the value_set get 'large', and takes two forms
 non-destructive (eg, can we merge constants into an existing interval
 with no loss of precision) and desctructive (creating intervals from
 the constants, or merging existing intervals).

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include "../variable_sensitivity_test_helpers.h"

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>

SCENARIO(
  "compacting value sets",
  "[core][analysis][variable-sensitivity][value_set_abstract_object][compact]")
{
  const typet type = signedbv_typet(32);
  const exprt val1 = from_integer(1, type);
  const exprt val2 = from_integer(2, type);
  const exprt val3 = from_integer(3, type);
  const exprt val4 = from_integer(4, type);
  const exprt val5 = from_integer(5, type);
  const exprt val6 = from_integer(6, type);
  const exprt val7 = from_integer(7, type);
  const exprt val8 = from_integer(8, type);
  const exprt val9 = from_integer(9, type);
  const exprt val10 = from_integer(10, type);
  const exprt val11 = from_integer(11, type);
  const exprt val12 = from_integer(12, type);
  const exprt interval_5_10 = constant_interval_exprt(val5, val10);
  const exprt interval_1_10 = constant_interval_exprt(val1, val10);

  auto config = vsd_configt::constant_domain();
  config.context_tracking.data_dependency_context = false;
  config.context_tracking.last_write_context = false;
  auto object_factory =
    variable_sensitivity_object_factoryt::configured_with(config);
  auto environment = abstract_environmentt{object_factory};
  environment.make_top();
  auto symbol_table = symbol_tablet{};
  auto ns = namespacet{symbol_table};

  GIVEN("compact values into existing interval")
  {
    WHEN("compacting { 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, [5, 10]")
    {
      auto value_set = make_value_set(
        {val1,
         val2,
         val3,
         val4,
         val5,
         val6,
         val7,
         val8,
         val9,
         val10,
         interval_5_10},
        environment,
        ns);
      THEN("{ 1, 2, 3, 4, [5, 10] }")
      {
        EXPECT(value_set, {val1, val2, val3, val4, interval_5_10});
      }
    }
    WHEN("compacting { 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, [1, 10]")
    {
      auto value_set = make_value_set(
        {val1,
         val2,
         val3,
         val4,
         val5,
         val6,
         val7,
         val8,
         val9,
         val10,
         interval_1_10},
        environment,
        ns);
      THEN("{ [1, 10] }")
      {
        EXPECT(value_set, {interval_1_10});
      }
    }
    WHEN("compacting { 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, [5, 10]")
    {
      auto value_set = make_value_set(
        {val1,
         val2,
         val3,
         val4,
         val5,
         val6,
         val7,
         val8,
         val9,
         val10,
         val11,
         val12,
         interval_5_10},
        environment,
        ns);
      THEN("{ 1, 2, 3, 4, 11, 12, [5, 10] }")
      {
        EXPECT(
          value_set, {val1, val2, val3, val4, val11, val12, interval_5_10});
      }
    }
    WHEN("compacting { 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, [1, 10], [5, 10]")
    {
      auto value_set = make_value_set(
        {val1,
         val2,
         val3,
         val4,
         val5,
         val6,
         val7,
         val8,
         val9,
         val10,
         interval_1_10,
         interval_5_10},
        environment,
        ns);
      THEN("{ [1, 10] }")
      {
        EXPECT(value_set, {interval_1_10});
      }
    }
    WHEN("compacting { 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, [5, 10], [1, 10]")
    {
      auto value_set = make_value_set(
        {val1,
         val2,
         val3,
         val4,
         val5,
         val6,
         val7,
         val8,
         val9,
         val10,
         val11,
         val12,
         interval_5_10,
         interval_1_10},
        environment,
        ns);
      THEN("{ 11, 12, [1, 10] }")
      {
        EXPECT(value_set, {val11, val12, interval_1_10});
      }
    }
  }
}