// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/smt_sorts.h>
#include <solvers/smt2_incremental/smt_terms.h>
#include <solvers/smt2_incremental/smt_to_string.h>

#include <util/mp_arith.h>

TEST_CASE("Test smt_sortt to string conversion", "[core][smt2_incremental]")
{
  CHECK(smt_to_string(smt_bool_sortt{}) == "Bool");
  CHECK(smt_to_string(smt_bit_vector_sortt{16}) == "(_ BitVec 16)");
}

TEST_CASE("Test smt_not_termt to string conversion", "[core][smt2_incremental]")
{
  CHECK(
    smt_to_string(smt_not_termt{
      smt_identifier_termt{"foo", smt_bool_sortt{}}}) == "(not |foo|)");
}

TEST_CASE(
  "Test smt_bit_vector_constant_termt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(smt_to_string(smt_bit_vector_constant_termt{0, 8}) == "(_ bv0 8)");
}

TEST_CASE(
  "Test smt_bool_literal_termt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(smt_to_string(smt_bool_literal_termt{true}) == "true");
  CHECK(smt_to_string(smt_bool_literal_termt{false}) == "false");
}

TEST_CASE(
  "Test smt_function_application_termt to string conversion",
  "[core][smt2_incremental]")
{
  CHECK(
    smt_to_string(smt_function_application_termt{
      smt_identifier_termt{"=", smt_bool_sortt{}},
      {smt_identifier_termt{"foo", smt_bit_vector_sortt{32}},
       {smt_identifier_termt{"bar", smt_bit_vector_sortt{32}}}}}) ==
    "(|=| |foo| |bar|)");
}
