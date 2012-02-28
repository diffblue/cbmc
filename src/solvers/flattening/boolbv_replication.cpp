/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <arith_tools.h>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_replication

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_replication(const exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());
  
  if(width==0)
    return conversion_failed(expr, bv);

  if(expr.operands().size()!=2)
    throw "replication takes two operands";

  mp_integer times;
  if(to_integer(expr.op0(), times))
    throw "replication takes constant as first parameter";

  const bvt &op=convert_bv(expr.op1());

  unsigned offset=0;
  bv.resize(width);

  for(unsigned i=0; i<integer2long(times); i++)
  {
    if(op.size()+offset>width)
      throw "replication operand width too big";

    for(unsigned i=0; i<op.size(); i++)
      bv[i+offset]=op[i];

    offset+=op.size();
  }    

  if(offset!=bv.size())
    throw "replication operand width too small";
}
