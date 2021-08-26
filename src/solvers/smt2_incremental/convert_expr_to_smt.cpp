// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/convert_expr_to_smt.h>

#include <util/expr.h>

smt_termt convert_expr_to_smt(const exprt &expr)
{
  UNIMPLEMENTED_FEATURE(
    "Generation of SMT formula for unknown kind of expression: " +
    expr.pretty());
}
