/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

#include <util/bitvector_types.h>

#include <solvers/floatbv/float_utils.h>

#include "boolbv.h"

bvt boolbvt::convert_floatbv_min_max(const binary_exprt &expr)
{
  if(expr.type().id() != ID_floatbv)
    return conversion_failed(expr);

  const bvt &bv0 = convert_bv(expr.lhs());
  const bvt &bv1 = convert_bv(expr.rhs());

  float_utilst float_utils(prop, to_floatbv_type(expr.type()));

  literalt x_nan = float_utils.is_NaN(bv0);
  literalt y_nan = float_utils.is_NaN(bv1);

  // IEEE 754-2019: if one operand is NaN, return the other
  // For min: return the smaller; ties (fp.eq) prefer negative sign
  // For max: return the larger; ties prefer positive sign
  literalt x_lt_y = float_utils.relation(bv0, float_utilst::relt::LT, bv1);
  literalt x_eq_y = float_utils.relation(bv0, float_utilst::relt::EQ, bv1);
  literalt x_sign = float_utilst::sign_bit(bv0);

  literalt prefer_x;
  if(expr.id() == ID_floatbv_min)
  {
    // min: prefer x if x < y, or if equal and x is negative
    prefer_x = prop.lor(x_lt_y, prop.land(x_eq_y, x_sign));
  }
  else
  {
    // max: prefer x if x > y, or if equal and x is positive
    literalt x_gt_y = float_utils.relation(bv0, float_utilst::relt::GT, bv1);
    prefer_x = prop.lor(x_gt_y, prop.land(x_eq_y, !x_sign));
  }

  bvt non_nan = bv_utils.select(prefer_x, bv0, bv1);
  bvt handle_y_nan = bv_utils.select(y_nan, bv0, non_nan);
  return bv_utils.select(x_nan, bv1, handle_y_nan);
}
