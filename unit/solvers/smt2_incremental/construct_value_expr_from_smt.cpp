// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/construct_value_expr_from_smt.h>

#include <solvers/smt2_incremental/smt_terms.h>
#include <solvers/smt2_incremental/smt_to_smt2_string.h>

#include <util/std_expr.h>
#include <util/std_types.h>

TEST_CASE("Value expr construction from smt.", "[core][smt2_incremental]")
{
  optionalt<smt_termt> input_term;
  optionalt<exprt> expected_result;

  using rowt = std::pair<smt_termt, exprt>;
  std::tie(input_term, expected_result) = GENERATE(
    rowt{smt_bool_literal_termt{true}, true_exprt{}},
    rowt{smt_bool_literal_termt{false}, false_exprt{}});
  SECTION(
    "Construction of \"" + id2string(expected_result->type().id()) +
    "\" from \"" + smt_to_smt2_string(*input_term) + "\"")
  {
    REQUIRE(
      construct_value_expr_from_smt(*input_term, expected_result->type()) ==
      *expected_result);
  }
}
