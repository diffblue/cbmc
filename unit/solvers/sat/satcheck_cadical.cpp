/*******************************************************************\

Module: Unit tests for satcheck_cadical

Author: Peter Schrammel, Michael Tautschnig

\*******************************************************************/

/// \file
/// Unit tests for satcheck_cadical

#ifdef HAVE_CADICAL

#  include <util/cout_message.h>

#  include <solvers/prop/literal.h>
#  include <solvers/sat/satcheck_cadical.h>
#  include <testing-utils/use_catch.h>

#  include <chrono>
#  include <cstddef>
#  include <vector>

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

  GIVEN("A pigeonhole formula PHP(20) and a 200-millisecond time limit")
  {
    // Same construction as the satcheck_minisat2 unit test: PHP(N) is
    // exponentially hard for resolution-based SAT solvers, so a
    // 200-millisecond time limit is reliably exceeded. Verifies that
    // the CaDiCaL `Terminator` we install is honoured by the
    // underlying solver.
    //
    // CaDiCaL polls the terminator at decision points; granularity is
    // therefore "shortly after the deadline". The five-second slack is
    // a generous bound for slow CI hardware and CaDiCaL's polling
    // interval.
    satcheck_cadical_no_preprocessingt satcheck(message_handler);
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
      REQUIRE(result == propt::resultt::P_ERROR);
      REQUIRE(elapsed_ms < 5000);
    }
  }
}

#endif
