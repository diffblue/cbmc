// Author: Diffblue Ltd.

#include <util/mp_arith.h>

#include <solvers/smt2_incremental/smt_array_theory.h>
#include <solvers/smt2_incremental/smt_bit_vector_theory.h>
#include <testing-utils/use_catch.h>

#include "testing-utils/invariant.h"

TEST_CASE("SMT array theory \"select\".", "[core][smt2_incremental]")
{
  const smt_identifier_termt index_term("index", smt_bit_vector_sortt(64));
  const smt_sortt value_sort(smt_bit_vector_sortt(32));
  const smt_identifier_termt array_term(
    "array", smt_array_sortt(index_term.get_sort(), value_sort));
  const smt_function_application_termt select =
    smt_array_theoryt::select(array_term, index_term);
  CHECK(select.get_sort() == value_sort);
  CHECK(select.function_identifier().identifier() == "select");
  REQUIRE(select.arguments().size() == 2);
  CHECK(select.arguments()[0].get() == array_term);
  CHECK(select.arguments()[1].get() == index_term);
  cbmc_invariants_should_throwt invariants_throw;
  const smt_bit_vector_constant_termt two{2, 8};
  REQUIRE_THROWS_MATCHES(
    smt_array_theoryt::select(two, index_term),
    invariant_failedt,
    invariant_failure_containing("\"select\" may only select from an array."));
  REQUIRE_THROWS_MATCHES(
    smt_array_theoryt::select(array_term, two),
    invariant_failedt,
    invariant_failure_containing(
      "Sort of arrays index must match the sort of the index supplied."));
}