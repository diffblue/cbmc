/*******************************************************************\

Module: Unit test helpers for SAT solver time limits

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Unit test helpers for SAT solver time limits

#ifndef CPROVER_SOLVERS_SAT_SAT_TIME_LIMIT_TEST_H
#define CPROVER_SOLVERS_SAT_SAT_TIME_LIMIT_TEST_H

#include <solvers/prop/literal.h>
#include <solvers/prop/prop.h>
#include <testing-utils/use_catch.h>

#include <chrono>
#include <cstddef>
#include <vector>

/// Add the pigeonhole formula PHP(\p holes) to \p solver: \p holes + 1
/// pigeons are each in some hole, and no two pigeons share a hole. The
/// formula is unsatisfiable, and exponentially hard for resolution-based SAT
/// solvers (Haken, 1985).
/// \return For each pigeon p and hole h, the literal that is true iff p is in
///   h.
inline std::vector<bvt> add_pigeonhole(propt &solver, std::size_t holes)
{
  const std::size_t pigeons = holes + 1;
  std::vector<bvt> in_hole(pigeons);
  for(auto &pigeon : in_hole)
    pigeon = solver.new_variables(holes);

  // each pigeon is in at least one hole
  for(const auto &pigeon : in_hole)
    solver.lcnf(pigeon);

  // no two pigeons share a hole
  for(std::size_t h = 0; h < holes; ++h)
  {
    for(std::size_t p1 = 0; p1 < pigeons; ++p1)
    {
      for(std::size_t p2 = p1 + 1; p2 < pigeons; ++p2)
        solver.lcnf(!in_hole[p1][h], !in_hole[p2][h]);
    }
  }

  return in_hole;
}

/// Check that a 200-millisecond time limit interrupts \p solver when solving
/// PHP(20), shortly after the limit has passed.
inline void check_time_limit(propt &solver)
{
  add_pigeonhole(solver, 20);
  solver.set_time_limit_milliseconds(200);

  const auto start = std::chrono::steady_clock::now();
  const auto result = solver.prop_solve();
  const auto elapsed_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                            std::chrono::steady_clock::now() - start)
                            .count();

  // The solver must report an error as it was interrupted, but not before the
  // time limit passed. The upper bound leaves generous slack for slow CI
  // machines and for the time it takes the solver to notice the interrupt.
  REQUIRE(result == propt::resultt::P_ERROR);
  REQUIRE(elapsed_ms >= 200);
  REQUIRE(elapsed_ms < 5000);
}

#endif // CPROVER_SOLVERS_SAT_SAT_TIME_LIMIT_TEST_H
