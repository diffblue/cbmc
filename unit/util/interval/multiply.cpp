/*******************************************************************\
 Module: Unit tests for variable/sensitivity/abstract_object::merge
 Author: DiffBlue Limited
\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/interval.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

#define V(X) (bvrep2integer(X.get(ID_value).c_str(), 32, true))
#define V_(X) (bvrep2integer(X.c_str(), 32, true))
#define CEV(X) (from_integer(mp_integer(X), signedbv_typet(32)))

SCENARIO("multiply interval domain", "[core][analyses][interval][multiply]")
{
  GIVEN("A selection of constant_exprts in a std::vector and map")
  {
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    WHEN("Single element multiplication")
    {
      constant_interval_exprt a(CEV(5));
      constant_interval_exprt b(CEV(10));
      const auto a_times_b = a.multiply(b);
      REQUIRE(a_times_b == constant_interval_exprt(CEV(50), CEV(50)));
    }

    WHEN("Both are positive [2,5]*[7,11]")
    {
      constant_interval_exprt a(CEV(2), CEV(5));
      constant_interval_exprt b(CEV(7), CEV(11));

      constant_interval_exprt result = constant_interval_exprt::multiply(a, b);

      THEN("Domain is consistent")
      {
        CHECK(V(a.get_lower()) == 2);
        CHECK(V(a.get_upper()) == 5);
        CHECK(V(b.get_lower()) == 7);
        CHECK(V(b.get_upper()) == 11);
      }

      CAPTURE(result);

      THEN("The result is [14, 55]")
      {
        CHECK(V(result.get_lower()) == 14);
        CHECK(V(result.get_upper()) == 55);
      }
    }

    WHEN("One is entirely negative [-2,-5]*[7,11]")
    {
      constant_interval_exprt a(CEV(-5), CEV(-2));
      constant_interval_exprt b(CEV(7), CEV(11));

      constant_interval_exprt result = constant_interval_exprt::multiply(a, b);

      THEN("Domain is consistent")
      {
        CHECK(V(a.get_lower()) == -5);
        CHECK(V(a.get_upper()) == -2);
        CHECK(V(b.get_lower()) == 7);
        CHECK(V(b.get_upper()) == 11);
      }

      CAPTURE(result);

      THEN("The result is [-55, -14]")
      {
        CHECK(V(result.get_lower()) == mp_integer(-55));
        CHECK(V(result.get_upper()) == -14);
      }
    }

    WHEN("Range contains and extends from zero [-2,5]*[7,11]")
    {
      constant_interval_exprt a(CEV(-2), CEV(5));
      constant_interval_exprt b(CEV(7), CEV(11));

      constant_interval_exprt result = constant_interval_exprt::multiply(a, b);

      THEN("Domain is consistent")
      {
        CHECK(V(a.get_lower()) == -2);
        CHECK(V(a.get_upper()) == 5);
        CHECK(V(b.get_lower()) == 7);
        CHECK(V(b.get_upper()) == 11);
      }

      CAPTURE(result);

      THEN("The result is [-22, 55]")
      {
        CHECK(V(result.get_lower()) == mp_integer(-22));
        CHECK(V(result.get_upper()) == 55);
      }
    }

    WHEN("One domain is infinite and other crosses zero [-2,5]*[7,INF]")
    {
      constant_interval_exprt a(CEV(-2), CEV(5));
      constant_interval_exprt b(CEV(7), max_exprt(signedbv_typet(32)));

      constant_interval_exprt result = constant_interval_exprt::multiply(a, b);

      THEN("Domain is consistent")
      {
        CHECK(V(a.get_lower()) == -2);
        CHECK(V(a.get_upper()) == 5);
        CHECK(V(b.get_lower()) == 7);

        CHECK(b.has_no_upper_bound());
      }

      CAPTURE(result);

      THEN("The result is [-INF, INF]")
      {
        CHECK(result.has_no_upper_bound());
        CHECK(result.has_no_lower_bound());
      }
    }

    WHEN("One domain is infinite and other is positive [2,5]*[7,INF]")
    {
      constant_interval_exprt a(CEV(2), CEV(5));
      constant_interval_exprt b(CEV(7), max_exprt(signedbv_typet(32)));
      constant_interval_exprt result = constant_interval_exprt::multiply(a, b);

      THEN("Domain is consistent")
      {
        CHECK(V(a.get_lower()) == 2);
        CHECK(V(a.get_upper()) == 5);
        CHECK(V(b.get_lower()) == 7);
        CHECK(b.has_no_upper_bound());
      }

      THEN("The result is [-INF, INF]")
      {
        CAPTURE(result);

        CHECK(result.has_no_upper_bound());
        CHECK(result.has_no_lower_bound());
      }
    }
  }
}
