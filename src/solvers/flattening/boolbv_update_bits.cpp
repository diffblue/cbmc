/*******************************************************************\

Module:

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/bitvector_expr.h>

#include "boolbv.h"

bvt boolbvt::convert_update_bits(const update_bits_exprt &expr)
{
  return convert_bv(expr.lower());
}
