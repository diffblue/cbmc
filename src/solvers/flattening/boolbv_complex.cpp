/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_complex

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_complex(const exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());
  
  if(width==0)
    return conversion_failed(expr, bv);
    
  bv.reserve(width);

  if(expr.type().id()==ID_complex)
  {
    const exprt::operandst &operands=expr.operands();
    
    if(operands.size()==2)
    {
      unsigned op_width=width/operands.size();
    
      forall_expr(it, operands)
      {
        const bvt &tmp=convert_bv(*it);

        if(tmp.size()!=op_width)
          throw "convert_complex: unexpected operand width";

        forall_literals(it2, tmp)
          bv.push_back(*it2);
      }   
    }

    return;
  }
  
  conversion_failed(expr, bv);
}

/*******************************************************************\

Function: boolbvt::convert_complex_real

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_complex_real(const exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());
  
  if(width==0)
    return conversion_failed(expr, bv);
    
  if(expr.operands().size()!=1)
    return conversion_failed(expr, bv);

  bv=convert_bv(expr.op0());

  assert(bv.size()==width*2);  
  bv.resize(width);
}

/*******************************************************************\

Function: boolbvt::convert_complex_imag

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_complex_imag(const exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());
  
  if(width==0)
    return conversion_failed(expr, bv);
    
  if(expr.operands().size()!=1)
    return conversion_failed(expr, bv);

  bv=convert_bv(expr.op0());

  assert(bv.size()==width*2);  
  bv.erase(bv.begin(), bv.begin()+width);
}

