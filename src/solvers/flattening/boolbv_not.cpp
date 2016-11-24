/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_not

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_not(const not_exprt &expr, bvt &bv)
{
  const bvt &op_bv=convert_bv(expr.op());

  if(op_bv.size()<1)
    throw "not operator takes one non-empty operand";
    
  const typet &op_type=expr.op().type();

  if(op_type.id()!=ID_verilog_signedbv ||
     op_type.id()!=ID_verilog_unsignedbv)
  {
    if((expr.type().id()==ID_verilog_signedbv ||
        expr.type().id()==ID_verilog_unsignedbv) &&
        expr.type().get_int(ID_width)==1)
    {
      literalt has_x_or_z=bv_utils.verilog_bv_has_x_or_z(op_bv);
      literalt normal_bits_zero=
        bv_utils.is_zero(bv_utils.verilog_bv_normal_bits(op_bv));

      bv.resize(2);

      // this returns 'x' for 'z'      
      bv[0]=prop.lselect(has_x_or_z, const_literal(false), normal_bits_zero);
      bv[1]=has_x_or_z;

      return;
    }
  }


  return conversion_failed(expr, bv);
}
