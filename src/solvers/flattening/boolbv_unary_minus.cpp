/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_types.h>

#include "boolbv.h"
#include "boolbv_type.h"

#include "../floatbv/float_utils.h"

bvt boolbvt::convert_unary_minus(const unary_exprt &expr)
{
  const typet &type=ns.follow(expr.type());

  std::size_t width=boolbv_width(type);

  if(width==0)
    return conversion_failed(expr);

  const exprt::operandst &operands=expr.operands();

  if(operands.size()!=1)
    throw "unary minus takes one operand";

  const exprt &op0=expr.op0();

  const bvt &op_bv=convert_bv(op0);

  bvtypet bvtype=get_bvtype(type);
  bvtypet op_bvtype=get_bvtype(op0.type());
  std::size_t op_width=op_bv.size();

  bool no_overflow=(expr.id()=="no-overflow-unary-minus");

  if(op_width==0 || op_width!=width)
    return conversion_failed(expr);

  if(bvtype==bvtypet::IS_UNKNOWN &&
     (type.id()==ID_vector || type.id()==ID_complex))
  {
    const typet &subtype=ns.follow(type.subtype());

    std::size_t sub_width=boolbv_width(subtype);

    if(sub_width==0 || width%sub_width!=0)
      throw "unary-: unexpected vector operand width";

    std::size_t size=width/sub_width;
    bvt bv;
    bv.resize(width);

    for(std::size_t i=0; i<size; i++)
    {
      bvt tmp_op;
      tmp_op.resize(sub_width);

      for(std::size_t j=0; j<tmp_op.size(); j++)
      {
        assert(i*sub_width+j<op_bv.size());
        tmp_op[j]=op_bv[i*sub_width+j];
      }

      bvt tmp_result;

      if(type.subtype().id()==ID_floatbv)
      {
        float_utilst float_utils(prop, to_floatbv_type(subtype));
        tmp_result=float_utils.negate(tmp_op);
      }
      else
        tmp_result=bv_utils.negate(tmp_op);

      assert(tmp_result.size()==sub_width);

      for(std::size_t j=0; j<tmp_result.size(); j++)
      {
        assert(i*sub_width+j<bv.size());
        bv[i*sub_width+j]=tmp_result[j];
      }
    }

    return bv;
  }
  else if(bvtype==bvtypet::IS_FIXED && op_bvtype==bvtypet::IS_FIXED)
  {
    if(no_overflow)
      return bv_utils.negate_no_overflow(op_bv);
    else
      return bv_utils.negate(op_bv);
  }
  else if(bvtype==bvtypet::IS_FLOAT && op_bvtype==bvtypet::IS_FLOAT)
  {
    assert(!no_overflow);
    float_utilst float_utils(prop, to_floatbv_type(expr.type()));
    return float_utils.negate(op_bv);
  }
  else if((op_bvtype==bvtypet::IS_SIGNED || op_bvtype==bvtypet::IS_UNSIGNED) &&
          (bvtype==bvtypet::IS_SIGNED || bvtype==bvtypet::IS_UNSIGNED))
  {
    if(no_overflow)
      prop.l_set_to(bv_utils.overflow_negate(op_bv), false);

    if(no_overflow)
      return bv_utils.negate_no_overflow(op_bv);
    else
      return bv_utils.negate(op_bv);
  }

  return conversion_failed(expr);
}
