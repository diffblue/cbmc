/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <std_types.h>

#include "boolbv.h"
#include "boolbv_type.h"

#ifdef HAVE_FLOATBV
#include "../floatbv/float_utils.h"
#endif

/*******************************************************************\

Function: boolbvt::convert_abs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_abs(const exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr, bv);

  const exprt::operandst &operands=expr.operands();

  if(operands.size()!=1)
    throw "abs takes one operand";
    
  const exprt &op0=expr.op0();

  const bvt &op_bv=convert_bv(op0);

  if(op0.type()!=expr.type())
    return conversion_failed(expr, bv);

  bvtypet bvtype=get_bvtype(expr.type());
  
  if(bvtype==IS_FIXED ||
     bvtype==IS_SIGNED ||
     bvtype==IS_UNSIGNED)
  {
    bv=bv_utils.absolute_value(op_bv);
    return;
  }
  else if(bvtype==IS_FLOAT)
  {
    #ifdef HAVE_FLOATBV
    float_utilst float_utils(prop);
    float_utils.spec=to_floatbv_type(expr.type());
    bv=float_utils.abs(op_bv);
    return;
    #endif
  }
  
  conversion_failed(expr, bv);
}
