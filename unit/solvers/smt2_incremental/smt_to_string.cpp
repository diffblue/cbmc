// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/smt_sorts.h>
#include <solvers/smt2_incremental/smt_to_string.h>

TEST_CASE("Test smt_sortt to string conversion", "[core][smt2_incremental]")
{
  CHECK(smt_to_string(smt_bool_sortt{}) == "Bool");
  CHECK(smt_to_string(smt_bit_vector_sortt{16}) == "(_ BitVec 16)");
}
