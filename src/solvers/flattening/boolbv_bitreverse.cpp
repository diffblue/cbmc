/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

#include <util/bitvector_expr.h>

#include "boolbv.h"

#include <algorithm>

bvt boolbvt::convert_bitreverse(const bitreverse_exprt &expr)
{
  const std::size_t width = boolbv_width(expr.type());

  bvt bv = convert_bv(expr.op(), width);

  std::reverse(bv.begin(), bv.end());

  return bv;
}
