/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/bitvector_types.h>

#include <solvers/floatbv/float_utils.h>

bvt boolbvt::convert_floatbv_mod_rem(const binary_exprt &expr)
{
  // Note that the expressions do not have rounding modes
  // but float_utils requires one.

  float_utilst float_utils(prop);

  auto rm = bv_utils.build_constant(ieee_floatt::ROUND_TO_EVEN, 32);
  float_utils.set_rounding_mode(rm);

  float_utils.spec = ieee_float_spect(to_floatbv_type(expr.type()));

  bvt lhs_as_bv = convert_bv(expr.lhs());
  bvt rhs_as_bv = convert_bv(expr.rhs());

  // float_utilst::rem implements lhs-(lhs/rhs)*rhs, which matches
  // neither fmod() nor IEEE
  return float_utils.rem(lhs_as_bv, rhs_as_bv);
}
