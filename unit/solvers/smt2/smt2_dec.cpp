// Author: Daniel Kroening, kroening@kroening.com

/// \file
/// Unit tests for smt2_solver_exit_code_expected

#include <testing-utils/use_catch.h>

#include <solvers/smt2/smt2_dec.h>

TEST_CASE(
  "smt2_solver_exit_code_expected classification",
  "[core][solvers][smt2]")
{
  using solvert = smt2_convt::solvert;

  const solvert all_solvers[] = {
    solvert::GENERIC,
    solvert::BITWUZLA,
    solvert::BOOLECTOR,
    solvert::CPROVER_SMT2,
    solvert::CVC3,
    solvert::CVC4,
    solvert::CVC5,
    solvert::MATHSAT,
    solvert::YICES,
    solvert::Z3};

  SECTION("a zero exit code is expected for every solver")
  {
    for(const auto solver : all_solvers)
      CHECK(smt2_solver_exit_code_expected(solver, 0));
  }

  SECTION("CPROVER_SMT2 expects exit code 20 for (error ...) responses")
  {
    CHECK(smt2_solver_exit_code_expected(solvert::CPROVER_SMT2, 20));
    CHECK_FALSE(smt2_solver_exit_code_expected(solvert::CPROVER_SMT2, 1));
    CHECK_FALSE(smt2_solver_exit_code_expected(solvert::CPROVER_SMT2, 10));
  }

  SECTION("Z3 expects exit code 1 when it emitted an (error ...) response")
  {
    CHECK(smt2_solver_exit_code_expected(solvert::Z3, 1));
    CHECK_FALSE(smt2_solver_exit_code_expected(solvert::Z3, 20));
    // Genuine z3 failures use distinct codes that must still be reported.
    CHECK_FALSE(smt2_solver_exit_code_expected(solvert::Z3, 101)); // memout
    CHECK_FALSE(smt2_solver_exit_code_expected(solvert::Z3, 102)); // timeout
    CHECK_FALSE(smt2_solver_exit_code_expected(solvert::Z3, 110)); // internal
  }

  SECTION("other solvers have no known benign non-zero exit code")
  {
    for(const auto solver :
        {solvert::GENERIC,
         solvert::BITWUZLA,
         solvert::BOOLECTOR,
         solvert::CVC3,
         solvert::CVC4,
         solvert::CVC5,
         solvert::MATHSAT,
         solvert::YICES})
    {
      CHECK_FALSE(smt2_solver_exit_code_expected(solver, 1));
      CHECK_FALSE(smt2_solver_exit_code_expected(solver, 20));
    }
  }
}
