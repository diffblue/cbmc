/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

bvt boolbvt::convert_concatenation(const exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  const exprt::operandst &operands=expr.operands();

  if(operands.empty())
    throw "concatenation takes at least one operand";

  std::size_t offset=width;
  bvt bv;
  bv.resize(width);

  forall_expr(it, operands)
  {
    const bvt &op=convert_bv(*it);

    if(op.size()>offset)
      throw "concatenation operand width too big";

    offset-=op.size();

    for(std::size_t i=0; i<op.size(); i++)
      bv[offset+i]=op[i];
  }

  if(offset!=0)
    throw "concatenation operand width too small";

  return bv;
}
