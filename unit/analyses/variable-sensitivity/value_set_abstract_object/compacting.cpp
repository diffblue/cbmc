/*******************************************************************\

 Module: Unit tests for value_set_abstract_valuet compacting

 Compacting occurs when the value_set get 'large', and takes two forms
 non-destructive (eg, can we merge constants into an existing interval
 with no loss of precision) and destructive (creating intervals from
 the constants, or merging existing intervals).

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>
#include <analyses/variable-sensitivity/variable_sensitivity_test_helpers.h>

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>
#include <util/symbol_table.h>

SCENARIO(
  "compacting value sets",
  "[core][analysis][variable-sensitivity][value_set_abstract_object][compact]")
{
  const typet type = signedbv_typet(32);
  auto val0 = from_integer(0, type);
  auto val1 = from_integer(1, type);
  auto val2 = from_integer(2, type);
  auto val3 = from_integer(3, type);
  auto val4 = from_integer(4, type);
  auto val5 = from_integer(5, type);
  auto val6 = from_integer(6, type);
  auto val7 = from_integer(7, type);
  auto val8 = from_integer(8, type);
  auto val9 = from_integer(9, type);
  auto val10 = from_integer(10, type);
  auto val11 = from_integer(11, type);
  auto val12 = from_integer(12, type);
  auto interval_5_10 = constant_interval_exprt(val5, val10);
  auto interval_1_10 = constant_interval_exprt(val1, val10);

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

  GIVEN("compact overlapping interval together")
  {
    auto interval_1_2 = constant_interval_exprt(val1, val2);
    auto interval_2_3 = constant_interval_exprt(val2, val3);
    auto interval_3_4 = constant_interval_exprt(val3, val4);
    auto interval_4_5 = constant_interval_exprt(val4, val5);
    auto interval_8_10 = constant_interval_exprt(val8, val10);
    auto interval_9_12 = constant_interval_exprt(val9, val12);
    auto val13 = from_integer(13, type);
    auto val14 = from_integer(14, type);
    auto val15 = from_integer(15, type);

    WHEN(
      "compacting { 0, [1, 2], [2, 3], [3, 4], [4, 5], 6, 7, [8, 10], [9, 12], "
      "13, 14, 15 }")
    {
      auto value_set = make_value_set(
        {val0,
         interval_1_2,
         interval_2_3,
         interval_3_4,
         interval_4_5,
         val6,
         val7,
         interval_8_10,
         interval_9_12,
         val13,
         val14,
         val15},
        environment,
        ns);
      THEN("{ 0, [1, 5], 6, 7, [9, 12], 13, 14, 15 }")
      {
        auto interval_1_5 = constant_interval_exprt(val1, val5);
        auto interval_8_12 = constant_interval_exprt(val8, val12);
        EXPECT(
          value_set,
          {val0, interval_1_5, val6, val7, interval_8_12, val13, val14, val15});
      }
    }
    WHEN(
      "compacting { [1, 2], [2, 3], [3, 4], [4, 5], [8, 10], [9, 12], 0, 1, 2, "
      "3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 }")
    {
      auto value_set = make_value_set(
        {val0,          val1,         val2,         val3,         val4,
         val5,          val6,         val7,         val8,         val9,
         val10,         val11,        val12,        val13,        val14,
         val15,         interval_1_2, interval_2_3, interval_3_4, interval_4_5,
         interval_8_10, interval_9_12},
        environment,
        ns);
      THEN("{ 0, [1, 5], 6, 7, [9, 12], 13, 14, 15 }")
      {
        auto interval_1_5 = constant_interval_exprt(val1, val5);
        auto interval_8_12 = constant_interval_exprt(val8, val12);
        EXPECT(
          value_set,
          {val0, interval_1_5, val6, val7, interval_8_12, val13, val14, val15});
      }
    }
  }

  GIVEN("compact values into new intervals")
  {
    WHEN("compacting { 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 }")
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
         val12},
        environment,
        ns);
      THEN("{ [1, 4], 5, 6, 7, 8, [9, 12] }")
      {
        auto interval_1_4 = constant_interval_exprt(val1, val4);
        auto interval_9_12 = constant_interval_exprt(val9, val12);

        EXPECT(
          value_set, {val5, val6, val7, val8, interval_1_4, interval_9_12});
      }
    }

    WHEN(
      "compacting { -100, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 100 } - pathalogical "
      "case with outliers")
    {
      auto val100minus = from_integer(-100, type);
      auto val100 = from_integer(100, type);
      auto value_set = make_value_set(
        {val100minus,
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
         val100},
        environment,
        ns);
      THEN("{ [-100, 0], [1, 100] }")
      {
        auto interval_100minus_0 = constant_interval_exprt(val100minus, val0);
        auto interval_1_100 = constant_interval_exprt(val1, val100);
        EXPECT(value_set, {interval_100minus_0, interval_1_100});
      }
    }
  }
}
