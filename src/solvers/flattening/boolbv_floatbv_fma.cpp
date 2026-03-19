/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

#include <util/bitvector_types.h>
#include <util/floatbv_expr.h>

#include <solvers/floatbv/float_utils.h>

#include "boolbv.h"

bvt boolbvt::convert_floatbv_fma(const floatbv_fma_exprt &expr)
{
  float_utilst float_utils(prop);

  float_utils.set_rounding_mode(convert_bv(expr.rounding_mode()));
  float_utils.spec = ieee_float_spect(to_floatbv_type(expr.type()));

  bvt multiply_lhs = convert_bv(expr.op_multiply_lhs());
  bvt multiply_rhs = convert_bv(expr.op_multiply_rhs());
  bvt addend = convert_bv(expr.op_add());

  return float_utils.fma(multiply_lhs, multiply_rhs, addend);
}
