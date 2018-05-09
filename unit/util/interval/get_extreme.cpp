/*******************************************************************\
 Module: Unit tests for variable/sensitivity/abstract_object::merge
 Author: DiffBlue Limited. All rights reserved.
\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/arith_tools.h>
#include <util/interval.h>
#include <util/mp_arith.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#define V(X) (binary2integer(X.get(ID_value).c_str(), 2))
#define V_(X) (binary2integer(X.c_str(), 2))

SCENARIO("get extreme exprt value", "[core][analyses][interval][get_extreme]")
{
  GIVEN("A selection of constant_exprts in a std::vector and map")
  {
    const typet type = signedbv_typet(32);
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    std::map<int, constant_exprt> values;
    std::vector<exprt> ve;

    for(int i = -100; i <= 100; i++)
    {
      values[i] = from_integer(mp_integer(i), type);
      ve.push_back(from_integer(mp_integer(i), type));
      //      values[i] = constant_exprt(std::to_string(i), integer_typet());;
      //      ve.push_back(exprt(constant_exprt(std::to_string(i), integer_typet())));
    }

    WHEN("-20 <= 20 is tested")
    {
      binary_predicate_exprt op1(values[-20], ID_le, values[20]);
      bool interval_eval =
        constant_interval_exprt::less_than_or_equal(values[-20], values[20]);
      simplify(op1, ns);

      THEN("Require it is TRUE")
      {
        REQUIRE(op1.is_true());
        REQUIRE(interval_eval);
      }
    }

    WHEN("20 <= -20 is tested")
    {
      binary_predicate_exprt op1(values[20], ID_le, values[-20]);
      bool interval_eval =
        constant_interval_exprt::less_than_or_equal(values[20], values[-20]);
      simplify(op1, ns);

      THEN("Require it is FALSE")
      {
        REQUIRE(op1.is_false());
        REQUIRE_FALSE(interval_eval);
      }
    }

    WHEN("-20 <= -20 is tested")
    {
      binary_predicate_exprt op1(values[-20], ID_le, values[-20]);
      bool interval_eval =
        constant_interval_exprt::less_than_or_equal(values[-20], values[-20]);

      simplify(op1, ns);

      THEN("Require it is TRUE")
      {
        REQUIRE(op1.is_true());
        REQUIRE(interval_eval);
        REQUIRE(constant_interval_exprt::equal(values[1], values[1]));
      }
    }

    WHEN("Two are selected and min found [20, -20]")
    {
      std::vector<exprt> selected = {values[20], values[-20]};

      exprt min = constant_interval_exprt::get_extreme(selected, true);
      exprt max = constant_interval_exprt::get_extreme(selected, false);

      THEN("Min (-20) and max (20) are verified")
      {
        CAPTURE(min.pretty());

        REQUIRE(V(min) == -20);
        REQUIRE(V(max) == 20);
      }
    }

    WHEN("Four are selected and min found [-20, 0, 20, 50]")
    {
      std::vector<exprt> selected = {
        values[-20], values[0], values[50], values[20]};

      exprt min = constant_interval_exprt::get_extreme(selected, true);
      exprt max = constant_interval_exprt::get_extreme(selected, false);

      THEN("Min (-20) and max (50) are verified")
      {
        REQUIRE(V(min) == -20);
        REQUIRE(V(max) == 50);
      }
    }

    WHEN("One is selected [-100]")
    {
      std::vector<exprt> selected = {values[-100]};

      exprt min = constant_interval_exprt::get_extreme(selected, true);
      exprt max = constant_interval_exprt::get_extreme(selected, false);

      THEN("Max (-100) and min (-100) are verified")
      {
        REQUIRE(V(min) == -100);
        REQUIRE(V(max) == -100);
      }
    }

    WHEN("Five are selected [20, 30, 15, 0, -100]")
    {
      std::vector<exprt> selected = {
        values[20], values[30], values[15], values[0], values[-100]};

      exprt min = constant_interval_exprt::get_extreme(selected, true);
      exprt max = constant_interval_exprt::get_extreme(selected, false);

      THEN("Max (30) and min (-100) are verified")
      {
        REQUIRE(V(min) == -100);
        REQUIRE(V(max) == 30);
      }
    }

    WHEN("All from [-100:100] are selected")
    {
      exprt min = constant_interval_exprt::get_extreme(ve, true);
      exprt max = constant_interval_exprt::get_extreme(ve, false);

      THEN("Max (100) and min (-100) are verified")
      {
        REQUIRE(V(min) == -100);
        REQUIRE(V(max) == 100);
      }
    }

    WHEN("All from [-100:100] are shuffled and selected")
    {
      std::random_shuffle(ve.begin(), ve.end());

      exprt min = constant_interval_exprt::get_extreme(ve, true);
      exprt max = constant_interval_exprt::get_extreme(ve, false);

      THEN("Max (100) and min (-100) are verified")
      {
        REQUIRE(V(min) == -100);
        REQUIRE(V(max) == 100);
      }
    }
  }
}
