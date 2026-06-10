/*******************************************************************\

Module: Unit tests for satcheck_cadical

Author: Peter Schrammel, Michael Tautschnig

\*******************************************************************/

/// \file
/// Unit tests for satcheck_cadical

#ifdef HAVE_CADICAL

#  include <util/cout_message.h>
#  include <util/invariant.h>

#  include <solvers/prop/literal.h>
#  include <solvers/sat/satcheck_cadical.h>
#  include <testing-utils/invariant.h>
#  include <testing-utils/use_catch.h>

SCENARIO("satcheck_cadical", "[core][solvers][sat][satcheck_cadical]")
{
  console_message_handlert message_handler;

  GIVEN("A satisfiable formula f")
  {
    satcheck_cadical_no_preprocessingt satcheck(message_handler);
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
    satcheck_cadical_no_preprocessingt satcheck(message_handler);
    literalt f = satcheck.new_variable();
    satcheck.l_set_to_true(satcheck.land(f, !f));

    THEN("is indeed unsatisfiable")
    {
      REQUIRE(satcheck.prop_solve() == propt::resultt::P_UNSATISFIABLE);
    }
  }

  GIVEN("An unsatisfiable formula false implied by a")
  {
    satcheck_cadical_no_preprocessingt satcheck(message_handler);
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
}

SCENARIO(
  "propt state machine",
  "[core][solvers][sat][satcheck_cadical][prop_state]")
{
  console_message_handlert message_handler;

  GIVEN("A fresh solver")
  {
    satcheck_cadical_no_preprocessingt satcheck(message_handler);

    THEN("initial state is UNKNOWN")
    {
      REQUIRE(satcheck.get_status() == propt::statust::UNKNOWN);
    }
  }

  GIVEN("A satisfiable formula")
  {
    satcheck_cadical_no_preprocessingt satcheck(message_handler);
    literalt f = satcheck.new_variable();
    satcheck.l_set_to_true(f);

    WHEN("solved")
    {
      auto result = satcheck.prop_solve();
      THEN("state is SAT")
      {
        REQUIRE(result == propt::resultt::P_SATISFIABLE);
        REQUIRE(satcheck.get_status() == propt::statust::SAT);
      }
      THEN("l_get returns a definite value")
      {
        REQUIRE(satcheck.l_get(f).is_true());
      }
    }
  }

  GIVEN("An unsatisfiable formula")
  {
    satcheck_cadical_no_preprocessingt satcheck(message_handler);
    literalt f = satcheck.new_variable();
    satcheck.l_set_to_true(satcheck.land(f, !f));

    WHEN("solved")
    {
      auto result = satcheck.prop_solve();
      THEN("state is UNSAT")
      {
        REQUIRE(result == propt::resultt::P_UNSATISFIABLE);
        REQUIRE(satcheck.get_status() == propt::statust::UNSAT);
      }
    }
  }

  GIVEN("A satisfiable formula that becomes unsatisfiable incrementally")
  {
    satcheck_cadical_no_preprocessingt satcheck(message_handler);
    literalt a = satcheck.new_variable();
    satcheck.set_frozen(a);
    satcheck.l_set_to_true(a);

    WHEN("first solve is SAT, then add contradicting clause")
    {
      REQUIRE(satcheck.prop_solve() == propt::resultt::P_SATISFIABLE);
      REQUIRE(satcheck.get_status() == propt::statust::SAT);
      REQUIRE(satcheck.l_get(a).is_true());

      // Adding a new clause transitions state back to UNKNOWN
      satcheck.l_set_to_false(a);
      REQUIRE(satcheck.get_status() == propt::statust::UNKNOWN);

      THEN("re-solving yields UNSAT")
      {
        REQUIRE(satcheck.prop_solve() == propt::resultt::P_UNSATISFIABLE);
        REQUIRE(satcheck.get_status() == propt::statust::UNSAT);
      }
    }

    WHEN("first solve is SAT, then add a new variable")
    {
      REQUIRE(satcheck.prop_solve() == propt::resultt::P_SATISFIABLE);
      REQUIRE(satcheck.get_status() == propt::statust::SAT);

      // Adding a new variable transitions state back to UNKNOWN
      satcheck.new_variable();
      REQUIRE(satcheck.get_status() == propt::statust::UNKNOWN);
    }
  }
}

SCENARIO(
  "propt state machine preconditions",
  "[core][solvers][sat][satcheck_cadical][prop_state]")
{
  console_message_handlert message_handler;
  const cbmc_invariants_should_throwt invariants_throw;

  GIVEN("A solver with a variable but no solve performed (UNKNOWN state)")
  {
    satcheck_cadical_no_preprocessingt satcheck(message_handler);
    const literalt v = satcheck.new_variable();
    REQUIRE(satcheck.get_status() == propt::statust::UNKNOWN);

    THEN("l_get() outside the SAT state fires its precondition")
    {
      REQUIRE_THROWS_AS(satcheck.l_get(v), invariant_failedt);
    }
    THEN("is_in_conflict() outside the UNSAT state fires its precondition")
    {
      REQUIRE_THROWS_AS(satcheck.is_in_conflict(v), invariant_failedt);
    }
  }

  GIVEN("A solver that has produced a SAT result")
  {
    satcheck_cadical_no_preprocessingt satcheck(message_handler);
    const literalt v = satcheck.new_variable();
    satcheck.set_frozen(v);
    satcheck.l_set_to_true(v);
    REQUIRE(satcheck.prop_solve() == propt::resultt::P_SATISFIABLE);

    THEN("is_in_conflict() (only valid in UNSAT) fires its precondition")
    {
      REQUIRE_THROWS_AS(satcheck.is_in_conflict(v), invariant_failedt);
    }
  }

  GIVEN("A solver that has produced an UNSAT result")
  {
    satcheck_cadical_no_preprocessingt satcheck(message_handler);
    const literalt v = satcheck.new_variable();
    satcheck.set_frozen(v);
    satcheck.l_set_to_true(satcheck.land(v, !v));
    REQUIRE(satcheck.prop_solve() == propt::resultt::P_UNSATISFIABLE);

    THEN("l_get() (only valid in SAT) fires its precondition")
    {
      REQUIRE_THROWS_AS(satcheck.l_get(v), invariant_failedt);
    }
  }
}

#endif
