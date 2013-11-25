/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_array(const exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr, bv);
    
  bv.reserve(width);

  if(expr.type().id()==ID_array)
  {
    assert(expr.has_operands());
    const exprt::operandst &operands=expr.operands();
    assert(!operands.empty());
    unsigned op_width=width/operands.size();
    
    forall_expr(it, operands)
    {
      const bvt &tmp=convert_bv(*it);

      if(tmp.size()!=op_width)
        throw "convert_array: unexpected operand width";

      forall_literals(it2, tmp)
        bv.push_back(*it2);
    }   

    return;
  }
  
  conversion_failed(expr, bv);
}

