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

SCENARIO("modulo interval domain", "[core][analyses][interval][modulo]")
{
  GIVEN("Two single element internvals")
  {
    constant_interval_exprt a(CEV(5));
    constant_interval_exprt b(CEV(10));
    constant_interval_exprt zero(CEV(0));
    const auto a_mod_b = a.modulo(b);
    REQUIRE(V(a_mod_b.get_upper()) == 5);

    const auto b_mod_a = b.modulo(a);
    // TODO: precision with single element modulo
    REQUIRE(V(b_mod_a.get_upper()) == 4);

    const auto zero_mod_a = zero.modulo(a);
    REQUIRE(zero_mod_a == constant_interval_exprt(CEV(0)));

    // TODO: this causes an invariant as it is unable to simplify the
    // TODO: simplify(a % 0) == a % 0
    // REQUIRE(a.modulo(zero).is_top());
  }
  GIVEN("Two simple signed intervals")
  {
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    WHEN("Positive RHS")
    {
      THEN("Ensure result is consistent.")
      {
        REQUIRE(
          constant_interval_exprt::modulo(
            constant_interval_exprt(CEV(10), CEV(20)),
            constant_interval_exprt(CEV(5), CEV(5))) ==
          constant_interval_exprt(CEV(0), CEV(4)));
        REQUIRE(
          constant_interval_exprt::modulo(
            constant_interval_exprt(CEV(10), CEV(20)),
            constant_interval_exprt(CEV(4), CEV(5))) ==
          constant_interval_exprt(CEV(0), CEV(4)));
        REQUIRE(
          constant_interval_exprt::modulo(
            constant_interval_exprt(CEV(10), CEV(20)),
            constant_interval_exprt(CEV(0), CEV(5))) ==
          constant_interval_exprt::top(signedbv_typet(32)));
        REQUIRE(
          constant_interval_exprt::modulo(
            constant_interval_exprt(CEV(10), CEV(20)),
            constant_interval_exprt(CEV(-5), CEV(5))) ==
          constant_interval_exprt::top(signedbv_typet(32)));

        INFO("Taking modulo on interval that contains zero results in top");
        REQUIRE(
          constant_interval_exprt::modulo(
            constant_interval_exprt(CEV(-10), CEV(20)),
            constant_interval_exprt(CEV(0), CEV(5))) ==
          constant_interval_exprt::top(signedbv_typet(32)));

        REQUIRE(
          constant_interval_exprt::modulo(
            constant_interval_exprt(CEV(-10), CEV(20)),
            constant_interval_exprt(CEV(1), CEV(5))) ==
          constant_interval_exprt(CEV(-10), CEV(20)));

        REQUIRE(
          constant_interval_exprt::modulo(
            constant_interval_exprt(CEV(-10), CEV(-1)),
            constant_interval_exprt(CEV(-5), CEV(-1))) ==
          constant_interval_exprt(CEV(-5), CEV(0)));

        REQUIRE(
          constant_interval_exprt::modulo(
            constant_interval_exprt(CEV(-20), CEV(-10)),
            constant_interval_exprt(CEV(0), CEV(5))) ==
          constant_interval_exprt::top(signedbv_typet(32)));

        REQUIRE(
          constant_interval_exprt::modulo(
            constant_interval_exprt(CEV(-20), CEV(-10)),
            constant_interval_exprt(CEV(1), CEV(1))) ==
          constant_interval_exprt(CEV(0)));

        REQUIRE(
          constant_interval_exprt::modulo(
            constant_interval_exprt(CEV(30), CEV(50)),
            constant_interval_exprt(CEV(2), CEV(2))) ==
          constant_interval_exprt(CEV(0), CEV(1)));

        // Problems
        REQUIRE(
          constant_interval_exprt::modulo(
            constant_interval_exprt(CEV(30), max_exprt(signedbv_typet(32))),
            constant_interval_exprt(CEV(2), CEV(2))) ==
          constant_interval_exprt(CEV(0), CEV(1)));
      }
    }
  }
}
