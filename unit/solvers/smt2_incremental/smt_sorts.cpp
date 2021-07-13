// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/smt_sorts.h>

TEST_CASE("Test smt_sortt.pretty is accessible.", "[core][smt2_incremental]")
{
  const smt_sortt bool_sort = smt_bool_sortt{};
  REQUIRE(bool_sort.pretty(0, 0) == "smt_bool_sort");
}

TEST_CASE(
  "Test smt_bit_vec_sortt bit_width getter.",
  "[core][smt2_incremental]")
{
  REQUIRE(smt_bit_vector_sortt{32}.bit_width() == 32);
}
