/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_types.h>

#include "boolbv.h"
#include "boolbv_type.h"

#include "../floatbv/float_utils.h"

/*******************************************************************\

Function: boolbvt::convert_abs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt boolbvt::convert_abs(const exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  const exprt::operandst &operands=expr.operands();

  if(operands.size()!=1)
    throw "abs takes one operand";

  const exprt &op0=expr.op0();

  const bvt &op_bv=convert_bv(op0);

  if(op0.type()!=expr.type())
    return conversion_failed(expr);

  bvtypet bvtype=get_bvtype(expr.type());

  if(bvtype==IS_FIXED ||
     bvtype==IS_SIGNED ||
     bvtype==IS_UNSIGNED)
  {
    return bv_utils.absolute_value(op_bv);
  }
  else if(bvtype==IS_FLOAT)
  {
    float_utilst float_utils(prop);
    float_utils.spec=to_floatbv_type(expr.type());
    return float_utils.abs(op_bv);
  }

  return conversion_failed(expr);
}
