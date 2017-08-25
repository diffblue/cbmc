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

  mp_integer times;
  if(to_integer(expr.op0(), times))
    throw "replication takes constant as first parameter";

  bvt bv;
  bv.resize(width);

  const std::size_t u_times=integer2unsigned(times);
  const bvt &op=convert_bv(expr.op1());
  std::size_t offset=0;

  for(std::size_t i=0; i<u_times; i++)
  {
    if(op.size()+offset>width)
      throw "replication operand width too big";

    for(std::size_t i=0; i<op.size(); i++)
      bv[i+offset]=op[i];

    offset+=op.size();
  }

  if(offset!=bv.size())
    throw "replication operand width too small";

  return bv;
}
