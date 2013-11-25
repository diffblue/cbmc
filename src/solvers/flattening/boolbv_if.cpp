/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_if(const exprt &expr, bvt &bv)
{
  const exprt::operandst &operands=expr.operands();
  
  unsigned width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr, bv);

  if(operands.size()!=3)
    throw "if takes three operands";

  literalt op0=convert(operands[0]);
  
  const bvt &op1_bv=convert_bv(operands[1]);
  const bvt &op2_bv=convert_bv(operands[2]);

  if(op1_bv.size()!=width || op2_bv.size()!=width)
    throw "operand size mismatch for if";

  bv=bv_utils.select(op0, op1_bv, op2_bv);
}
