/*******************************************************************\

Module: Unit tests for solvers/flattening/boolbv_onehot

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file

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

TEST_CASE("onehot flattening", "[core][solvers][flattening][boolbvt][onehot]")
{
  console_message_handlert message_handler;
  message_handler.set_verbosity(0);
  satcheckt satcheck{message_handler};
  boolbvt boolbv{empty_namespace, satcheck, message_handler};
  unsignedbv_typet u8{8};

  GIVEN("A bit-vector that is one-hot")
  {
    boolbv << onehot_exprt{from_integer(64, u8)};

    THEN("the lowering of onehot is true")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
    }
  }

  GIVEN("A bit-vector that is not one-hot")
  {
    boolbv << onehot_exprt{from_integer(5, u8)};

    THEN("the lowering of onehot is false")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_UNSATISFIABLE);
    }
  }

  GIVEN("A bit-vector that is not one-hot")
  {
    boolbv << onehot_exprt{from_integer(0, u8)};

    THEN("the lowering of onehot is false")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_UNSATISFIABLE);
    }
  }

  GIVEN("A bit-vector that is one-hot 0")
  {
    boolbv << onehot0_exprt{from_integer(0xfe, u8)};

    THEN("the lowering of onehot0 is true")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
    }
  }

  GIVEN("A bit-vector that is not one-hot 0")
  {
    boolbv << onehot0_exprt{from_integer(0x7e, u8)};

    THEN("the lowering of onehot0 is false")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_UNSATISFIABLE);
    }
  }

  GIVEN("A bit-vector that is not one-hot 0")
  {
    boolbv << onehot0_exprt{from_integer(0xff, u8)};

    THEN("the lowering of onehot0 is false")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_UNSATISFIABLE);
    }
  }
}
