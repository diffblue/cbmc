/*******************************************************************\

Module: Unit tests for boolbvt

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Unit tests for boolbvt

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/cout_message.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>
#include <testing-utils/empty_namespace.h>
#include <testing-utils/use_catch.h>

SCENARIO(
  "boolbvt_update_bit",
  "[core][solvers][flattening][boolbvt][update_bit]")
{
  console_message_handlert message_handler;
  message_handler.set_verbosity(0);

  GIVEN("A satisfiable bit-vector formula f with update_bit")
  {
    satcheckt satcheck{message_handler};
    boolbvt boolbv{empty_namespace, satcheck, message_handler};

    unsignedbv_typet u32{32};
    boolbv << equal_exprt(
      symbol_exprt{"x", u32},
      update_bit_exprt{from_integer(10, u32), 0, true_exprt{}});

    THEN("is indeed satisfiable")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
    }
  }
}
