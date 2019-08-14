/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/std_types.h>

#include "boolbv_type.h"

#include <solvers/floatbv/float_utils.h>

literalt boolbvt::convert_ieee_float_rel(const binary_relation_exprt &expr)
{
  const exprt::operandst &operands=expr.operands();
  const irep_idt &rel=expr.id();

  if(operands.size()==2)
  {
    const exprt &op0=expr.op0();
    const exprt &op1=expr.op1();

    bvtypet bvtype0=get_bvtype(op0.type());
    bvtypet bvtype1=get_bvtype(op1.type());

    const bvt &bv0=convert_bv(op0);
    const bvt &bv1=convert_bv(op1);

    if(bv0.size()==bv1.size() && !bv0.empty() &&
       bvtype0==bvtypet::IS_FLOAT && bvtype1==bvtypet::IS_FLOAT)
    {
      float_utilst float_utils(prop, to_floatbv_type(op0.type()));

      if(rel==ID_ieee_float_equal)
        return float_utils.relation(bv0, float_utilst::relt::EQ, bv1);
      else if(rel==ID_ieee_float_notequal)
        return !float_utils.relation(bv0, float_utilst::relt::EQ, bv1);
      else
        return SUB::convert_rest(expr);
    }
  }

  return SUB::convert_rest(expr);
}
