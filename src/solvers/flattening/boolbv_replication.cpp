/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>

bvt boolbvt::convert_replication(const replication_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  mp_integer times = numeric_cast_v<mp_integer>(expr.times());

  bvt bv;
  bv.resize(width);

  const std::size_t u_times = numeric_cast_v<std::size_t>(times);
  const bvt &op = convert_bv(expr.op());

  INVARIANT(
    op.size() * u_times == bv.size(),
    "result bitvector width shall be equal to the operand bitvector width times"
    "the number of replications");

  std::size_t bit_idx = 0;

  for(std::size_t i = 0; i < u_times; i++)
  {
    for(const auto &bit : op)
    {
      bv[bit_idx] = bit;
      bit_idx++;
    }
  }

  return bv;
}
