/*******************************************************************\

Module: Unit tests for boolbvt

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Unit tests for boolbvt

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/cout_message.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>
#include <testing-utils/use_catch.h>

SCENARIO("boolbvt", "[core][solvers][flattening][boolbvt]")
{
  console_message_handlert message_handler;
  message_handler.set_verbosity(0);

  GIVEN("A satisfiable bit-vector formula f")
  {
    satcheckt satcheck(message_handler);
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    boolbvt boolbv(ns, satcheck, message_handler);

    unsignedbv_typet u32(32);
    boolbv << equal_exprt(symbol_exprt("x", u32), from_integer(10, u32));

    THEN("is indeed satisfiable")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
    }
    THEN("is unsatisfiable under an inconsistent assumption")
    {
      auto assumption =
        equal_exprt(symbol_exprt("x", u32), from_integer(11, u32));
      REQUIRE(
        boolbv(assumption) == decision_proceduret::resultt::D_UNSATISFIABLE);
    }
  }
}
