/*******************************************************************\

Module: Unit tests for checking the integration of SMT switch

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

// only enable the tests if compiling with SMT switch
#ifdef HAVE_SMT_SWITCH
#  include <cvc4_factory.h>
#  include <smt.h>
#endif

#include <vector>

TEST_CASE("Trivial SMT switch using CVC4", "[core][solvers][smt-switch]")
{
#ifdef HAVE_SMT_SWITCH
  smt::SmtSolver s = smt::CVC4SolverFactory::create();
  s->set_opt("produce-models", "true");
  smt::Sort bvsort32 = s->make_sort(smt::BV, 32);
  smt::Sort array32_32 = s->make_sort(smt::ARRAY, bvsort32, bvsort32);
  smt::Term x = s->make_term("x", bvsort32);
  smt::Term y = s->make_term("y", bvsort32);
  smt::Term arr = s->make_term("arr", array32_32);

  s->assert_formula(s->make_term(
    smt::Not,
    s->make_term(
      smt::Implies,
      s->make_term(smt::Equal, x, y),
      s->make_term(
        smt::Equal,
        s->make_term(smt::Select, arr, x),
        s->make_term(smt::Select, arr, y)))));
  REQUIRE_FALSE(s->check_sat().is_sat());
#else
  INFO("SMT switch test disabled");
#endif
}
