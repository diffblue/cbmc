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

#  include <chrono>
#  include <cstddef>
#  include <vector>

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
  }

  GIVEN("A pigeonhole formula PHP(20) and a 200-millisecond time limit")
  {
    // Same construction as the satcheck_minisat2 unit test: PHP(N) is
    // exponentially hard for resolution-based SAT solvers, so a
    // 200-millisecond time limit is reliably exceeded. Verifies that
    // the IPASIR `ipasir_set_terminate` callback we install is
    // honoured by the underlying solver.
    satcheck_ipasirt satcheck(message_handler);
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
      // The solver must report P_ERROR (terminate callback fired)
      // and not have run far past the budget. The 5-second slack is
      // for slow CI hardware.
      REQUIRE(result == propt::resultt::P_ERROR);
      REQUIRE(elapsed_ms >= 200);
      REQUIRE(elapsed_ms < 5000);
    }
  }
}

#endif
