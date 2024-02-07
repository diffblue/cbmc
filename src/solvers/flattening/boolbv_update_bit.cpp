/*******************************************************************\

Module:

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/bitvector_expr.h>

#include "boolbv.h"

bvt boolbvt::convert_update_bit(const update_bit_exprt &expr)
{
  return convert_bv(expr.lower());
}
