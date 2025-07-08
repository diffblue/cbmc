/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

#include <util/bitvector_expr.h>

#include "boolbv.h"

bvt boolbvt::convert_popcount(const popcount_exprt &expr)
{
  const std::size_t width = boolbv_width(expr.type());

  bvt op = convert_bv(expr.op());

  return bv_utils.zero_extension(bv_utils.popcount(op), width);
}
