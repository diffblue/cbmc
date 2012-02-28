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

Function: boolbvt::convert_unary_minus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_unary_minus(const exprt &expr, bvt &bv)
{
  const typet &type=ns.follow(expr.type());

  unsigned width=boolbv_width(type);
  
  if(width==0)
    return conversion_failed(expr, bv);

  const exprt::operandst &operands=expr.operands();

  if(operands.size()!=1)
    throw "unary minus takes one operand";
    
  const exprt &op0=expr.op0();

  const bvt &op_bv=convert_bv(op0);

  bvtypet bvtype=get_bvtype(type);
  bvtypet op_bvtype=get_bvtype(op0.type());
  unsigned op_width=op_bv.size();

  bool no_overflow=(expr.id()=="no-overflow-unary-minus");
  
  if(op_width==0 || op_width!=width)
    return conversion_failed(expr, bv);

  if(bvtype==IS_UNKNOWN &&
     type.id()==ID_vector)
  {
    const typet &subtype=ns.follow(type.subtype());
  
    unsigned sub_width=boolbv_width(subtype);

    if(sub_width==0 || width%sub_width!=0)
      throw "unary-: unexpected vector operand width";

    unsigned size=width/sub_width;
    bv.resize(width);

    for(unsigned i=0; i<size; i++)
    {
      bvt tmp_op;
      tmp_op.resize(sub_width);

      for(unsigned j=0; j<tmp_op.size(); j++)
      {
        assert(i*sub_width+j<op_bv.size());
        tmp_op[j]=op_bv[i*sub_width+j];
      }
      
      bvt tmp_result;
      
      if(type.subtype().id()==ID_floatbv)
      {
        #ifdef HAVE_FLOATBV
        float_utilst float_utils(prop);
        float_utils.spec=to_floatbv_type(subtype);
        tmp_result=float_utils.negate(tmp_op);
        #else
        return conversion_failed(expr, bv);
        #endif
      }
      else
        tmp_result=bv_utils.negate(tmp_op);
    
      assert(tmp_result.size()==sub_width);
      
      for(unsigned j=0; j<tmp_result.size(); j++)
      {
        assert(i*sub_width+j<bv.size());
        bv[i*sub_width+j]=tmp_result[j];
      }
    }

    return;
  }
  else if(bvtype==IS_FIXED && op_bvtype==IS_FIXED)
  {
    if(no_overflow)
      bv=bv_utils.negate_no_overflow(op_bv);
    else
      bv=bv_utils.negate(op_bv);

    return;
  }
  else if(bvtype==IS_FLOAT && op_bvtype==IS_FLOAT)
  {
    #ifdef HAVE_FLOATBV
    assert(!no_overflow);
    float_utilst float_utils(prop);
    float_utils.spec=to_floatbv_type(expr.type());
    bv=float_utils.negate(op_bv);
    return;
    #endif
  }
  else if((op_bvtype==IS_SIGNED || op_bvtype==IS_UNSIGNED) &&
          (bvtype==IS_SIGNED || bvtype==IS_UNSIGNED))
  {
    if(no_overflow)
      prop.l_set_to(bv_utils.overflow_negate(op_bv), false);

    if(no_overflow)
      bv=bv_utils.negate_no_overflow(op_bv);
    else
      bv=bv_utils.negate(op_bv);

    return;
  }

  conversion_failed(expr, bv);
}
