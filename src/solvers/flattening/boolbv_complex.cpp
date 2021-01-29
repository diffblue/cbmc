/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/invariant.h>

bvt boolbvt::convert_complex(const complex_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  DATA_INVARIANT(
    expr.type().id() == ID_complex,
    "complex expression shall have complex type");

  bvt bv;
  bv.reserve(width);

  const exprt::operandst &operands = expr.operands();
  std::size_t op_width = width / operands.size();

  for(const auto &op : operands)
  {
    const bvt &tmp = convert_bv(op, op_width);

    bv.insert(bv.end(), tmp.begin(), tmp.end());
  }

  return bv;
}

bvt boolbvt::convert_complex_real(const complex_real_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  bvt bv = convert_bv(expr.op(), width * 2);

  bv.resize(width); // chop

  return bv;
}

bvt boolbvt::convert_complex_imag(const complex_imag_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  bvt bv = convert_bv(expr.op(), width * 2);

  bv.erase(bv.begin(), bv.begin()+width);

  return bv;
}
