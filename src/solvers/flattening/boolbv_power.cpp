/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/mathematical_expr.h>

#include "boolbv.h"

bvt boolbvt::convert_power(const power_exprt &expr)
{
  const typet &type = expr.type();

  std::size_t width=boolbv_width(type);

  if(type.id()==ID_unsignedbv ||
     type.id()==ID_signedbv)
  {
    // Let's do the special case 2**x
    bvt base = convert_bv(expr.base());
    bvt exponent = convert_bv(expr.exponent());

    literalt eq_2 =
      bv_utils.equal(base, bv_utils.build_constant(2, base.size()));

    bvt one=bv_utils.build_constant(1, width);
    bvt shift = bv_utils.shift(one, bv_utilst::shiftt::SHIFT_LEFT, exponent);

    bvt nondet=prop.new_variables(width);

    return bv_utils.select(eq_2, shift, nondet);
  }

  return conversion_failed(expr);
}
