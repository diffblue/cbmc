/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_bitwise

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_bitwise(const exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());
  
  if(width==0)
    return conversion_failed(expr, bv);

  if(expr.id()==ID_bitnot)
  {
    if(expr.operands().size()!=1)
      throw "bitnot takes one operand";

    const exprt &op0=expr.op0();
    
    const bvt &op_bv=convert_bv(op0);

    bv.resize(width);
    
    if(op_bv.size()!=width)
      throw "convert_bitwise: unexpected operand width";

    for(unsigned i=0; i<width; i++)
      bv[i]=prop.lnot(op_bv[i]);

    return;
  }
  else if(expr.id()==ID_bitand || expr.id()==ID_bitor ||
          expr.id()==ID_bitxor)
  {
    bv.resize(width);

    for(unsigned i=0; i<width; i++)
      bv[i]=const_literal(expr.id()==ID_bitand);
    
    forall_operands(it, expr)
    {
      const bvt &op=convert_bv(*it);

      if(op.size()!=width)
        throw "convert_bitwise: unexpected operand width";

      for(unsigned i=0; i<width; i++)
      {
        if(expr.id()==ID_bitand)
          bv[i]=prop.land(bv[i], op[i]);
        else if(expr.id()==ID_bitor)
          bv[i]=prop.lor(bv[i], op[i]);
        else if(expr.id()==ID_bitxor)
          bv[i]=prop.lxor(bv[i], op[i]);
        else
          throw "unexpected operand";
      }
    }    

    return;
  }
 
  throw "unexpected bitwise operand";
}
