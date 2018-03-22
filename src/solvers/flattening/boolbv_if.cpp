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

  const bvt &cond_bv = convert_bv(expr.cond());
  CHECK_RETURN(cond_bv.size() == 1);
  literalt cond = cond_bv[0];

  const bvt &true_case_bv = convert_bv(expr.true_case(), width);
  const bvt &false_case_bv = convert_bv(expr.false_case(), width);

  return bv_utils.select(cond, true_case_bv, false_case_bv);
}
