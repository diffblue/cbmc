/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "boolbv.h"

bvt boolbvt::convert_power(const binary_exprt &expr)
{
  const typet &type = expr.type();

  std::size_t width=boolbv_width(type);

  if(width==0)
    return conversion_failed(expr);

  if(type.id()==ID_unsignedbv ||
     type.id()==ID_signedbv)
  {
    // Let's do the special case 2**x
    bvt op0=convert_bv(expr.op0());
    bvt op1=convert_bv(expr.op1());

    literalt eq_2=
      bv_utils.equal(op0, bv_utils.build_constant(2, op0.size()));

    bvt one=bv_utils.build_constant(1, width);
    bvt shift=bv_utils.shift(one, bv_utilst::shiftt::SHIFT_LEFT, op1);

    bvt nondet=prop.new_variables(width);

    return bv_utils.select(eq_2, shift, nondet);
  }

  return conversion_failed(expr);
}
