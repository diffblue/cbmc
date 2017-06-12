/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

bvt boolbvt::convert_if(const if_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return bvt(); // An empty bit-vector if.

  literalt cond=convert(expr.cond());

  const bvt &op1_bv=convert_bv(expr.true_case());
  const bvt &op2_bv=convert_bv(expr.false_case());

  if(op1_bv.size()!=width || op2_bv.size()!=width)
    throw "operand size mismatch for if "+expr.pretty();

  return bv_utils.select(cond, op1_bv, op2_bv);
}
