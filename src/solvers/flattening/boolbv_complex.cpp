/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "boolbv.h"

bvt boolbvt::convert_complex(const exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  if(expr.type().id()==ID_complex)
  {
    const exprt::operandst &operands=expr.operands();

    bvt bv;
    bv.reserve(width);

    if(operands.size()==2)
    {
      std::size_t op_width=width/operands.size();

      forall_expr(it, operands)
      {
        const bvt &tmp=convert_bv(*it);

        if(tmp.size()!=op_width)
          throw "convert_complex: unexpected operand width";

        forall_literals(it2, tmp)
          bv.push_back(*it2);
      }
    }

    return bv;
  }

  return conversion_failed(expr);
}

bvt boolbvt::convert_complex_real(const complex_real_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  bvt bv = convert_bv(expr.op());

  assert(bv.size()==width*2);
  bv.resize(width); // chop

  return bv;
}

bvt boolbvt::convert_complex_imag(const complex_imag_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  bvt bv = convert_bv(expr.op());

  assert(bv.size()==width*2);
  bv.erase(bv.begin(), bv.begin()+width);

  return bv;
}
