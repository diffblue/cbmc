// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/smt_core_theory.h>
#include <solvers/smt2_incremental/smt_terms.h>

#include <util/mp_arith.h>

TEST_CASE("SMT core theory \"not\".", "[core][smt2_incremental]")
{
  const smt_bool_literal_termt operand{true};
  const auto not_term = smt_core_theoryt::make_not(operand);

  CHECK(not_term.get_sort() == smt_bool_sortt{});
  CHECK(
    not_term.function_identifier() ==
    smt_identifier_termt{"not", smt_bool_sortt{}});
  REQUIRE(not_term.arguments().size() == 1);
  REQUIRE(not_term.arguments()[0].get() == operand);
  cbmc_invariants_should_throwt invariants_throw;
  CHECK_THROWS(smt_core_theoryt::make_not(smt_bit_vector_constant_termt{0, 1}));
}
