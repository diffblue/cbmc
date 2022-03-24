/*******************************************************************\
 Module: Unit tests for variable/sensitivity/abstract_object::merge
 Author: DiffBlue Limited
\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/interval.h>
#include <util/mp_arith.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/symbol_table.h>

#include <testing-utils/use_catch.h>

#include <random>

#define V(X) (bvrep2integer(X.get(ID_value).c_str(), 32, true))
#define V_(X) (bvrep2integer(X.c_str(), 32, true))
#define CEV(X) (from_integer(mp_integer(X), signedbv_typet(32)))

SCENARIO("get extreme exprt value", "[core][analyses][interval][get_extreme]")
{
  GIVEN("A selection of constant_exprts in a std::vector and map")
  {
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    std::vector<exprt> ve;

    for(int i = -100; i <= 100; i++)
    {
      ve.push_back(from_integer(mp_integer(i), signedbv_typet(32)));
    }
    WHEN("-20 <= 20 is tested")
    {
      binary_predicate_exprt op1(CEV(-20), ID_le, CEV(20));
      bool interval_eval =
        constant_interval_exprt::less_than_or_equal(CEV(-20), CEV(20));
      simplify(op1, ns);

      THEN("Require it is TRUE")
      {
        REQUIRE(op1.is_true());
        REQUIRE(interval_eval);
      }
    }

    WHEN("20 <= -20 is tested")
    {
      binary_predicate_exprt op1(CEV(20), ID_le, CEV(-20));
      bool interval_eval =
        constant_interval_exprt::less_than_or_equal(CEV(20), CEV(-20));
      simplify(op1, ns);

      THEN("Require it is FALSE")
      {
        REQUIRE(op1.is_false());
        REQUIRE_FALSE(interval_eval);
      }
    }

    WHEN("-20 <= -20 is tested")
    {
      binary_predicate_exprt op1(CEV(-20), ID_le, CEV(-20));
      bool interval_eval =
        constant_interval_exprt::less_than_or_equal(CEV(-20), CEV(-20));

      simplify(op1, ns);

      THEN("Require it is TRUE")
      {
        REQUIRE(op1.is_true());
        REQUIRE(interval_eval);
        REQUIRE(constant_interval_exprt::equal(CEV(1), CEV(1)));
      }
    }

    WHEN("Two are selected and min found [20, -20]")
    {
      std::vector<exprt> selected = {CEV(20), CEV(-20)};

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
      std::vector<exprt> selected = {CEV(-20), CEV(0), CEV(50), CEV(20)};

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
      std::vector<exprt> selected = {CEV(-100)};

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
        CEV(20), CEV(30), CEV(15), CEV(0), CEV(-100)};

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
      std::random_device rd;
      std::mt19937 g(rd());
      std::shuffle(ve.begin(), ve.end(), g);

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
