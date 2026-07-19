/*******************************************************************\

Module: Unit tests for satcheck_minisat2

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Unit tests for satcheck_minisat2

#ifdef HAVE_MINISAT2

#  include <util/cout_message.h>

#  include <solvers/prop/literal.h>
#  include <solvers/sat/satcheck_minisat2.h>
#  include <testing-utils/use_catch.h>

#  include <chrono>
#  include <cstddef>
#  include <vector>

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

  GIVEN("A pigeonhole formula PHP(20) and a 200-millisecond time limit")
  {
    // The pigeonhole principle: N+1 pigeons cannot all fit in N holes
    // (one pigeon per hole). For N=20 the resulting CNF is provably
    // exponentially hard for resolution-based SAT solvers (Haken,
    // 1985), so a 200-millisecond time limit is reliably blown
    // through.
    satcheck_minisat_no_simplifiert satcheck(message_handler);
    constexpr std::size_t holes = 20;
    constexpr std::size_t pigeons = holes + 1;
    std::vector<std::vector<literalt>> x(pigeons);
    for(std::size_t p = 0; p < pigeons; ++p)
    {
      x[p].reserve(holes);
      for(std::size_t h = 0; h < holes; ++h)
        x[p].push_back(satcheck.new_variable());
    }
    // Each pigeon is in at least one hole.
    for(std::size_t p = 0; p < pigeons; ++p)
    {
      bvt clause = x[p];
      satcheck.lcnf(clause);
    }
    // No two pigeons share a hole.
    for(std::size_t h = 0; h < holes; ++h)
      for(std::size_t p1 = 0; p1 < pigeons; ++p1)
        for(std::size_t p2 = p1 + 1; p2 < pigeons; ++p2)
        {
          bvt clause;
          clause.push_back(!x[p1][h]);
          clause.push_back(!x[p2][h]);
          satcheck.lcnf(clause);
        }

    satcheck.set_time_limit_milliseconds(200);

    THEN("the solver returns P_ERROR (interrupted by the time limit)")
    {
      const auto start = std::chrono::steady_clock::now();
      const auto result = satcheck.prop_solve();
      const auto elapsed_ms =
        std::chrono::duration_cast<std::chrono::milliseconds>(
          std::chrono::steady_clock::now() - start)
          .count();
      // The solver must report P_ERROR (it was interrupted by the
      // watchdog thread) and must not have run far past the
      // 200-millisecond budget. The 5-second slack is for very slow
      // CI hardware and any latency in joining the watchdog thread.
      // The lower bound guards against a regression that fires the
      // watchdog before the deadline (e.g. a stale interrupt flag).
      REQUIRE(result == propt::resultt::P_ERROR);
      REQUIRE(elapsed_ms >= 200);
      REQUIRE(elapsed_ms < 5000);
    }
  }

  GIVEN("A checker whose interrupt flag has been left set")
  {
    // Simulate the race in which the watchdog called interrupt() just as a
    // previous solve was returning, leaving MiniSat's (sticky) asynch_interrupt
    // flag latched. do_prop_solve() must clear it, otherwise this trivially
    // satisfiable solve would spuriously report P_ERROR. This pins down the
    // --all-properties / --cover / incremental-loop regression.
    satcheck_minisat_no_simplifiert satcheck(message_handler);
    literalt f = satcheck.new_variable();
    satcheck.l_set_to_true(f);
    satcheck.interrupt();

    THEN("the next solve clears the flag and reports P_SATISFIABLE")
    {
      REQUIRE(satcheck.prop_solve() == propt::resultt::P_SATISFIABLE);
    }
  }
}

#endif
