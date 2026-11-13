/*******************************************************************\

Module: Unit tests for satcheck_ipasir

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Unit tests for satcheck_ipasir, focusing on the time-limit
/// (`set_time_limit_milliseconds`) plumbing that hooks into the IPASIR
/// `ipasir_set_terminate` mechanism.

#ifdef HAVE_IPASIR

#  include <util/cout_message.h>

#  include <solvers/prop/literal.h>
#  include <solvers/sat/satcheck_ipasir.h>
#  include <testing-utils/use_catch.h>

#  include "sat_time_limit_test.h"

SCENARIO("satcheck_ipasir", "[core][solvers][sat][satcheck_ipasir]")
{
  console_message_handlert message_handler;
  message_handler.set_verbosity(0);

  GIVEN("A satisfiable formula f")
  {
    satcheck_ipasirt satcheck(message_handler);
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
      REQUIRE(
        satcheck.prop_solve(assumptions) == propt::resultt::P_UNSATISFIABLE);
    }
  }

  GIVEN("An unsatisfiable formula f && !f")
  {
    satcheck_ipasirt satcheck(message_handler);
    literalt f = satcheck.new_variable();
    satcheck.l_set_to_true(satcheck.land(f, !f));

    THEN("is indeed unsatisfiable")
    {
      REQUIRE(satcheck.prop_solve() == propt::resultt::P_UNSATISFIABLE);
    }
  }

  GIVEN("An unsatisfiable formula false implied by a")
  {
    satcheck_ipasirt satcheck(message_handler);
    literalt a = satcheck.new_variable();
    literalt a_implies_false = satcheck.lor(!a, const_literal(false));
    satcheck.l_set_to_true(a_implies_false);

    THEN("is indeed unsatisfiable under assumption a")
    {
      bvt assumptions;
      assumptions.push_back(a);
      REQUIRE(
        satcheck.prop_solve(assumptions) == propt::resultt::P_UNSATISFIABLE);
    }
    THEN("is still unsatisfiable under assumption a and true")
    {
      bvt assumptions;
      assumptions.push_back(const_literal(true));
      assumptions.push_back(a);
      REQUIRE(
        satcheck.prop_solve(assumptions) == propt::resultt::P_UNSATISFIABLE);
    }
    THEN("becomes satisfiable when assumption a is lifted")
    {
      bvt assumptions;
      REQUIRE(
        satcheck.prop_solve(assumptions) == propt::resultt::P_SATISFIABLE);
    }
  }

  GIVEN("A pigeonhole formula PHP(20) and a 200-millisecond time limit")
  {
    satcheck_ipasirt satcheck(message_handler);

    THEN("the solver is interrupted by the time limit")
    {
      check_time_limit(satcheck);
    }
  }
}

#endif
