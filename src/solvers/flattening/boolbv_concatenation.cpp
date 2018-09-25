/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/invariant.h>

bvt boolbvt::convert_concatenation(const concatenation_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  const exprt::operandst &operands=expr.operands();

  DATA_INVARIANT(
    !operands.empty(), "concatentation shall have at least one operand");

  std::size_t offset=width;
  bvt bv;
  bv.resize(width);

  forall_expr(it, operands)
  {
    const bvt &op=convert_bv(*it);

    INVARIANT(
      op.size() <= offset,
      "concatentation operand must fit into the result bitvector");

    offset-=op.size();

    for(std::size_t i=0; i<op.size(); i++)
      bv[offset+i]=op[i];
  }

  INVARIANT(
    offset == 0,
    "all bits in the result bitvector must have been filled up by the "
    "concatentation operands");

  return bv;
}
