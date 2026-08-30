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
  message_handler.set_verbosity(0);

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
      REQUIRE(
        satcheck.prop_solve(assumptions) == propt::resultt::P_UNSATISFIABLE);
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

  GIVEN("A simplifying solver with incremental simplification limited")
  {
    satcheck_minisat_simplifiert satcheck(message_handler);
    satcheck.set_limit_incremental_simplification();

    literalt a = satcheck.new_variable();
    // freeze so the simplifier does not eliminate the variable we assume on
    satcheck.set_frozen(a);
    satcheck.l_set_to_true(a);

    THEN("incremental solves remain correct after the first (simplifying) call")
    {
      // first solve runs the simplifier; subsequent solves run with the
      // simplifier disabled (do_simp == false)
      REQUIRE(satcheck.prop_solve() == propt::resultt::P_SATISFIABLE);
      bvt assumptions;
      assumptions.push_back(!a);
      REQUIRE(
        satcheck.prop_solve(assumptions) == propt::resultt::P_UNSATISFIABLE);
      REQUIRE(satcheck.prop_solve() == propt::resultt::P_SATISFIABLE);
    }
  }

  GIVEN("A non-simplifying solver")
  {
    satcheck_minisat_no_simplifiert satcheck(message_handler);

    THEN("set_limit_incremental_simplification is a no-op and solving works")
    {
      // the propt default is a no-op for non-simplifying back-ends
      propt &prop = satcheck;
      prop.set_limit_incremental_simplification();

      literalt f = satcheck.new_variable();
      satcheck.l_set_to_true(f);
      REQUIRE(satcheck.prop_solve() == propt::resultt::P_SATISFIABLE);
    }
  }
}

#endif
