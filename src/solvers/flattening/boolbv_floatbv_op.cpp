/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <std_types.h>

#include "boolbv.h"

#include "../floatbv/float_utils.h"

/*******************************************************************\

Function: boolbvt::convert_floatbv_op

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_floatbv_op(const exprt &expr, bvt &bv)
{
  const typet &type=ns.follow(expr.type());

  // TODO: complex and vector  
  if(type.id()!=ID_floatbv)
    return conversion_failed(expr, bv);

  unsigned width=boolbv_width(type);
  
  if(width==0)
    return conversion_failed(expr, bv);
    
  const exprt::operandst &operands=expr.operands();

  if(operands.size()!=3)
    throw "operator "+expr.id_string()+" takes three operands";

  const exprt &op0=expr.op0();
  const exprt &op1=expr.op1();
  const exprt &op2=expr.op2();

  if(op0.type()!=type || op1.type()!=type)
  {
    std::cerr << expr.pretty() << std::endl;
    throw "float op with mixed types";
  }

  bvt bv0=convert_bv(op0);
  bvt bv1=convert_bv(op1);
  bvt bv2=convert_bv(op2);

  float_utilst float_utils(prop);
  float_utils.spec=to_floatbv_type(expr.type());

  if(expr.id()==ID_floatbv_plus)
    bv=float_utils.add_sub(bv0, bv1, false);
  else if(expr.id()==ID_floatbv_minus)
    bv=float_utils.add_sub(bv0, bv1, true);
  else if(expr.id()==ID_floatbv_mult)
    bv=float_utils.mul(bv0, bv1);
  else if(expr.id()==ID_floatbv_div)
    bv=float_utils.div(bv0, bv1);
  else
    assert(false);
}

