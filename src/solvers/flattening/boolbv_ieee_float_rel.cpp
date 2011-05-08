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

Function: boolbvt::convert_ieee_float_rel

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolbvt::convert_ieee_float_rel(const exprt &expr)
{
  #ifdef HAVE_FLOATBV
  const exprt::operandst &operands=expr.operands();
  const std::string &rel=expr.id_string();

  if(operands.size()==2)
  {
    const exprt &op0=expr.op0();
    const exprt &op1=expr.op1();

    bvt bv0, bv1;
    bvtypet bvtype0=get_bvtype(op0.type());
    bvtypet bvtype1=get_bvtype(op1.type());

    convert_bv(op0, bv0);
    convert_bv(op1, bv1);
    
    if(bv0.size()==bv1.size() && bv0.size()!=0 &&
       bvtype0==IS_FLOAT && bvtype1==IS_FLOAT)
    {
      float_utilst float_utils(prop);
      float_utils.spec=to_floatbv_type(op0.type());

      if(rel=="ieee_float_equal")
        return float_utils.relation(bv0, float_utilst::EQ, bv1);
      else if(rel=="ieee_float_notequal")
        return prop.lnot(float_utils.relation(bv0, float_utilst::EQ, bv1));
      else
        return SUB::convert_rest(expr);
    }
  }
  #endif

  return SUB::convert_rest(expr);
}

