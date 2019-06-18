/*******************************************************************\

Module: Unit tests for satcheck_minisat2

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Unit tests for satcheck_minisat2

#ifdef HAVE_MINISAT2

#  include <testing-utils/use_catch.h>

#  include <solvers/prop/literal.h>
#  include <solvers/sat/satcheck_minisat2.h>
#  include <util/cout_message.h>

SCENARIO("satcheck_minisat2", "[core][solvers][sat][satcheck_minisat2]")
{
  console_message_handlert message_handler;

  GIVEN("A satisfiable formula f")
  {
    satcheck_minisat_no_simplifiert satcheck(message_handler);
    literalt f = satcheck.new_variable();
    satcheck.l_set_to_true(f);

    THEN("is indeed satisfiable")
    {
      REQUIRE(satcheck.prop_solve() == propt::resultt::P_SATISFIABLE);
    }
    THEN("is unsatisfiable under a false assumption")
    {
      bvt assumptions;
      assumptions.push_back(const_literal(false));
      satcheck.set_assumptions(assumptions);
      REQUIRE(satcheck.prop_solve() == propt::resultt::P_UNSATISFIABLE);
    }
  }

  GIVEN("An unsatisfiable formula f && !f")
  {
    satcheck_minisat_no_simplifiert satcheck(message_handler);
    literalt f = satcheck.new_variable();
    satcheck.l_set_to_true(satcheck.land(f, !f));

    THEN("is indeed unsatisfiable")
    {
      REQUIRE(satcheck.prop_solve() == propt::resultt::P_UNSATISFIABLE);
    }
  }

  GIVEN("An unsatisfiable formula false implied by a")
  {
    satcheck_minisat_no_simplifiert satcheck(message_handler);
    literalt a = satcheck.new_variable();
    literalt a_implies_false = satcheck.lor(!a, const_literal(false));
    satcheck.l_set_to_true(a_implies_false);

    THEN("is indeed unsatisfiable under assumption a")
    {
      bvt assumptions;
      assumptions.push_back(a);
      satcheck.set_assumptions(assumptions);
      REQUIRE(satcheck.prop_solve() == propt::resultt::P_UNSATISFIABLE);
    }
    THEN("is still unsatisfiable under assumption a and true")
    {
      bvt assumptions;
      assumptions.push_back(const_literal(true));
      assumptions.push_back(a);
      satcheck.set_assumptions(assumptions);
      REQUIRE(satcheck.prop_solve() == propt::resultt::P_UNSATISFIABLE);
    }
    THEN("becomes satisfiable when assumption a is lifted")
    {
      bvt assumptions;
      satcheck.set_assumptions(assumptions);
      REQUIRE(satcheck.prop_solve() == propt::resultt::P_SATISFIABLE);
    }
  }
}

#endif
