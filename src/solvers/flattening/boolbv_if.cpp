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

  const bvt &true_case_bv = convert_bv(expr.true_case());
  const bvt &false_case_bv = convert_bv(expr.false_case());

  DATA_INVARIANT(
    true_case_bv.size() == width && false_case_bv.size() == width,
    "true and false case of an if expression must have the same type as"
    " the overall expression");

  return bv_utils.select(cond, true_case_bv, false_case_bv);
}
