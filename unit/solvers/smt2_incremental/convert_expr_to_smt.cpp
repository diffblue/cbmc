// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/convert_expr_to_smt.h>
#include <solvers/smt2_incremental/smt_terms.h>

#include <util/std_expr.h>

TEST_CASE("expr to smt conversion for bool literal", "[core][smt2_incremental]")
{
  CHECK(convert_expr_to_smt(true_exprt{}) == smt_bool_literal_termt{true});
  CHECK(convert_expr_to_smt(false_exprt{}) == smt_bool_literal_termt{false});
}
