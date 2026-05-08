/*******************************************************************\

Module: Unit tests for bv_utilst

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Unit tests for bv_utilst

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/cout_message.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>
#include <testing-utils/use_catch.h>

SCENARIO("1-bit signed less-than", "[core][solvers][flattening][bv_utils]")
{
  console_message_handlert message_handler;
  message_handler.set_verbosity(0);

  GIVEN("Two 1-bit signed bitvector symbols")
  {
    satcheckt satcheck(message_handler);
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    boolbvt boolbv(ns, satcheck, message_handler);

    signedbv_typet s1(1);
    auto x = symbol_exprt("x", s1);
    auto y = symbol_exprt("y", s1);

    THEN("-1 < 0 is satisfiable")
    {
      // x = -1, y = 0, x < y
      boolbv << equal_exprt(x, from_integer(-1, s1));
      boolbv << equal_exprt(y, from_integer(0, s1));
      boolbv << less_than_exprt(x, y);
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
    }

    THEN("0 < -1 is unsatisfiable")
    {
      boolbv << equal_exprt(x, from_integer(0, s1));
      boolbv << equal_exprt(y, from_integer(-1, s1));
      boolbv << less_than_exprt(x, y);
      REQUIRE(boolbv() == decision_proceduret::resultt::D_UNSATISFIABLE);
    }

    THEN("-1 <= -1 is satisfiable")
    {
      boolbv << equal_exprt(x, from_integer(-1, s1));
      boolbv << equal_exprt(y, from_integer(-1, s1));
      boolbv << less_than_or_equal_exprt(x, y);
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
    }

    THEN("-1 < -1 is unsatisfiable")
    {
      boolbv << equal_exprt(x, from_integer(-1, s1));
      boolbv << equal_exprt(y, from_integer(-1, s1));
      boolbv << less_than_exprt(x, y);
      REQUIRE(boolbv() == decision_proceduret::resultt::D_UNSATISFIABLE);
    }

    THEN("x < y is satisfiable for symbolic 1-bit signed values")
    {
      boolbv << less_than_exprt(x, y);
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
    }

    THEN("x <= y is satisfiable for symbolic 1-bit signed values")
    {
      boolbv << less_than_or_equal_exprt(x, y);
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
    }
  }
}
