/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_shift

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_shift(const exprt &expr, bvt &bv)
{
  const irep_idt &type_id=expr.type().id();

  if(type_id!=ID_unsignedbv &&
     type_id!=ID_signedbv &&
     type_id!=ID_floatbv &&
     type_id!=ID_pointer &&
     type_id!=ID_bv)
    return conversion_failed(expr, bv);

  unsigned width=boolbv_width(expr.type());
  
  if(width==0)
    return conversion_failed(expr, bv);

  if(expr.operands().size()!=2)
    throw "shifting takes two operands";

  const bvt &op=convert_bv(expr.op0());
  const bvt &dist=convert_bv(expr.op1());

  if(op.size()!=width)
    throw "convert_shift: unexpected operand width";

  bv_utilst::shiftt shift;

  if(expr.id()==ID_shl)
    shift=bv_utilst::LEFT;
  else if(expr.id()==ID_ashr)
    shift=bv_utilst::ARIGHT;
  else if(expr.id()==ID_lshr)
    shift=bv_utilst::LRIGHT;
  else
    throw "unexpected operand";

  bv=bv_utils.shift(op, shift, dist);
}
