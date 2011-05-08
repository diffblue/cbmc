/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_concatenation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_concatenation(const exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());
  
  if(width==0)
    return conversion_failed(expr, bv);
    
  const exprt::operandst &operands=expr.operands();

  if(operands.size()==0)
    throw "concatenation takes at least one operand";

  unsigned offset=width;
  bv.resize(width);

  forall_expr(it, operands)
  {
    bvt op;

    convert_bv(*it, op);

    if(op.size()>offset)
      throw "concatenation operand width too big";

    offset-=op.size();

    for(unsigned i=0; i<op.size(); i++)
      bv[offset+i]=op[i];
  }    

  if(offset!=0)
    throw "concatenation operand width too small";
}
