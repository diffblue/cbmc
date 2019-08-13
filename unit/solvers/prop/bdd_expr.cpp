/*******************************************************************\

Module: Unit tests for bdd_expr

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Unit tests for bdd_expr

#include <testing-utils/use_catch.h>

#include <solvers/prop/bdd_expr.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

SCENARIO("bdd_expr", "[core][solver][prop][bdd_expr]")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  bdd_exprt bdd_expr_converter;

  GIVEN("A bdd for x&!x")
  {
    const symbol_exprt var("x", bool_typet());
    const bddt bdd =
      bdd_expr_converter.from_expr(and_exprt(var, not_exprt(var)));
    REQUIRE(bdd_expr_converter.as_expr(bdd) == false_exprt());
  }

  GIVEN("A bdd for (a&b)|!a")
  {
    const symbol_exprt a("a", bool_typet());
    const symbol_exprt b("b", bool_typet());

    const bddt bdd =
      bdd_expr_converter.from_expr(or_exprt(and_exprt(a, b), not_exprt(a)));

    THEN("It is equal to the BDD for (!a|b)")
    {
      const bddt bdd2 = bdd_expr_converter.from_expr(or_exprt(not_exprt(a), b));
      REQUIRE(
        bdd_expr_converter.as_expr(bdd) == bdd_expr_converter.as_expr(bdd2));
    }
  }

  GIVEN("A bdd for (a&!b)")
  {
    const symbol_exprt a("a", bool_typet());
    const symbol_exprt b("b", bool_typet());

    const bddt bdd = bdd_expr_converter.from_expr(and_exprt(a, not_exprt(b)));

    WHEN("It is converted to an exprt")
    {
      const exprt result = bdd_expr_converter.as_expr(bdd);
      THEN("It is equivalent to the expression !(!a || b)")
      {
        const bddt to_compare =
          bdd_expr_converter.from_expr(not_exprt{or_exprt{not_exprt{a}, b}});
        REQUIRE(bdd.bdd_xor(to_compare).is_false());
        REQUIRE(bdd.bdd_xor(to_compare.bdd_not()).is_true());
      }
    }
  }

  GIVEN("(!a | b) xor (a => b) ")
  {
    const symbol_exprt a("a", bool_typet());
    const symbol_exprt b("b", bool_typet());
    const bddt bdd = bdd_expr_converter.from_expr(
      xor_exprt{or_exprt{not_exprt{a}, b}, implies_exprt{a, b}});
    THEN("It reduces to false")
    {
      REQUIRE(bdd.is_false());
    }
  }

  GIVEN("e = (a | b) xor (c | d)")
  {
    const symbol_exprt a("a", bool_typet());
    const symbol_exprt b("b", bool_typet());
    const symbol_exprt c("c", bool_typet());
    const symbol_exprt d("d", bool_typet());

    const xor_exprt expr{or_exprt{a, b}, or_exprt{c, d}};
    const bddt bdd = bdd_expr_converter.from_expr(expr);

    THEN("e xor e is false")
    {
      REQUIRE(bdd.bdd_xor(bdd_expr_converter.from_expr(expr)).is_false());
    }

    THEN("e xor !e is true")
    {
      REQUIRE(
        bdd.bdd_xor(bdd_expr_converter.from_expr(not_exprt{expr})).is_true());
    }

    THEN("Converting to expr and back to BDD gives the same BDD")
    {
      const exprt expr_of_bdd = bdd_expr_converter.as_expr(bdd);
      const bddt bdd_of_expr = bdd_expr_converter.from_expr(expr_of_bdd);
      REQUIRE(bdd_of_expr.equals(bdd));
    }
  }
}
