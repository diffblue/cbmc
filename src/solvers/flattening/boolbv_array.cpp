/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

bvt boolbvt::convert_array(const exprt &expr)
{
  const std::size_t width = boolbv_width(expr.type());
  if(width==0)
    return conversion_failed(expr);

  if(expr.type().id()==ID_array)
  {
    INVARIANT(expr.has_operands(), "array should have operands");
    const exprt::operandst &operands=expr.operands();
    const std::size_t op_width = width / operands.size();
    bvt bv;
    bv.reserve(width);

    for(const exprt &op : operands)
    {
      const bvt &tmp = convert_bv(op);
      CHECK_RETURN(tmp.size() == op_width);
      bv.insert(bv.end(), tmp.begin(), tmp.end());
    }

    return bv;
  }
  return conversion_failed(expr);
}
