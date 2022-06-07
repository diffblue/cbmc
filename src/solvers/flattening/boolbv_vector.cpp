/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "boolbv.h"

bvt boolbvt::convert_vector(const vector_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  const exprt::operandst &operands = expr.operands();

  bvt bv;
  bv.reserve(width);

  if(!operands.empty())
  {
    std::size_t op_width = width / operands.size();

    for(const auto &op : operands)
    {
      const bvt &tmp = convert_bv(op, op_width);

      bv.insert(bv.end(), tmp.begin(), tmp.end());
    }
  }

  return bv;
}
