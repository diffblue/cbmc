/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/invariant.h>

bvt boolbvt::convert_array(const exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  if(expr.type().id()==ID_array)
  {
    DATA_INVARIANT(
      expr.has_operands(),
      "the bit width being nonzero implies that the array has a nonzero size "
      "in which case the array shall have operands");
    const exprt::operandst &operands=expr.operands();
    std::size_t op_width=width/operands.size();

    bvt bv;
    bv.reserve(width);

    forall_expr(it, operands)
    {
      const bvt &tmp = convert_bv(*it, op_width);

      forall_literals(it2, tmp)
        bv.push_back(*it2);
    }

    return bv;
  }

  return conversion_failed(expr);
}
