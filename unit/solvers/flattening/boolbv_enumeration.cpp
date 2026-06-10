/*******************************************************************\

Module: Unit tests for solvers/flattening

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file

#include <util/cout_message.h>
#include <util/namespace.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>
#include <testing-utils/empty_namespace.h>
#include <testing-utils/use_catch.h>

TEST_CASE(
  "enumeration flattening",
  "[core][solvers][flattening][boolbvt][enumeration]")
{
  console_message_handlert message_handler;
  message_handler.set_verbosity(0);
  satcheckt satcheck{message_handler};
  boolbvt boolbv{empty_namespace, satcheck, message_handler};
  enumeration_typet enumeration;
  enumeration.elements().push_back(irept{"A"});
  enumeration.elements().push_back(irept{"B"});

  constant_exprt A("A", enumeration);
  constant_exprt B("B", enumeration);

  GIVEN("an inconsistent equality over an enumeration type")
  {
    boolbv << equal_exprt{A, B};

    THEN("the formula is unsat")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_UNSATISFIABLE);
    }
  }

  GIVEN("an equality over an enumeration type")
  {
    symbol_exprt symbol("s", enumeration);
    boolbv << equal_exprt{symbol, A};

    THEN("the value of the variable in the model is correct")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
      REQUIRE(boolbv.get(symbol) == A);
    }
  }
}
