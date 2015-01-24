/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_union(const union_exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr, bv);

  const bvt &op_bv=convert_bv(expr.op());

  if(width<op_bv.size())
    throw "union: unexpected operand op width";

  bv.resize(width);
  
  for(unsigned i=0; i<op_bv.size(); i++)
    bv[i]=op_bv[i];

  // pad with nondets
  for(unsigned i=op_bv.size(); i<bv.size(); i++)
    bv[i]=prop.new_variable();
}
