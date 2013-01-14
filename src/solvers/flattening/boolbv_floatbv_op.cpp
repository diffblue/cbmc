/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>
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
  const exprt::operandst &operands=expr.operands();

  if(operands.size()!=3)
    throw "operator "+expr.id_string()+" takes three operands";

  const exprt &op0=expr.op0();
  const exprt &op1=expr.op1();
  const exprt &op2=expr.op2();

  bvt bv0=convert_bv(op0);
  bvt bv1=convert_bv(op1);
  bvt bv2=convert_bv(op2);

  const typet &type=ns.follow(expr.type());

  if(op0.type()!=type || op1.type()!=type)
  {
    std::cerr << expr.pretty() << std::endl;
    throw "float op with mixed types";
  }

  float_utilst float_utils(prop);

  // TODO: complex and vector  
  if(type.id()==ID_floatbv)
  {
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
  else if(type.id()==ID_vector || type.id()==ID_complex)
  {
    const typet &subtype=ns.follow(type.subtype());
    
    if(subtype.id()==ID_floatbv)
    {
      float_utils.spec=to_floatbv_type(subtype);

      unsigned width=boolbv_width(type);
      unsigned sub_width=boolbv_width(subtype);

      if(sub_width==0 || width%sub_width!=0)
        throw "convert_floatbv_op: unexpected vector operand width";

      unsigned size=width/sub_width;
      bv.resize(width);

      for(unsigned i=0; i<size; i++)
      {
        bvt tmp_bv0, tmp_bv1, tmp_bv;
        
        tmp_bv0.assign(bv0.begin()+i*sub_width, bv0.begin()+(i+1)*sub_width);
        tmp_bv1.assign(bv1.begin()+i*sub_width, bv1.begin()+(i+1)*sub_width);

        if(expr.id()==ID_floatbv_plus)
          tmp_bv=float_utils.add_sub(tmp_bv0, tmp_bv1, false);
        else if(expr.id()==ID_floatbv_minus)
          tmp_bv=float_utils.add_sub(tmp_bv0, tmp_bv1, true);
        else if(expr.id()==ID_floatbv_mult)
          tmp_bv=float_utils.mul(tmp_bv0, tmp_bv1);
        else if(expr.id()==ID_floatbv_div)
          tmp_bv=float_utils.div(tmp_bv0, tmp_bv1);
        else
          assert(false);

        assert(tmp_bv.size()==sub_width);
        assert(i*sub_width+sub_width-1<bv.size());
        std::copy(tmp_bv.begin(), tmp_bv.end(), bv.begin()+i*sub_width);
      }
    }
  }
  else
    return conversion_failed(expr, bv);
}

