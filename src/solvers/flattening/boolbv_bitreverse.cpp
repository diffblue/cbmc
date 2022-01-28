/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

#include "boolbv.h"

#include <util/bitvector_expr.h>

bvt boolbvt::convert_bitreverse(const bitreverse_exprt &expr)
{
  const std::size_t width = boolbv_width(expr.type());
  if(width == 0)
    return conversion_failed(expr);

  bvt bv = convert_bv(expr.op(), width);

  std::reverse(bv.begin(), bv.end());

  return bv;
}
