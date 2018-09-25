/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "boolbv.h"

bvt boolbvt::convert_bitwise(const exprt &expr)
{
  const std::size_t width = boolbv_width(expr.type());
  if(width==0)
    return conversion_failed(expr);

  if(expr.id()==ID_bitnot)
  {
    DATA_INVARIANT(expr.operands().size() == 1, "bitnot takes one operand");
    const exprt &op0=expr.op0();
    const bvt &op_bv = convert_bv(op0, width);
    return bv_utils.inverted(op_bv);
  }
  else if(expr.id()==ID_bitand || expr.id()==ID_bitor ||
          expr.id()==ID_bitxor ||
          expr.id()==ID_bitnand || expr.id()==ID_bitnor ||
          expr.id()==ID_bitxnor)
  {
    bvt bv;
    bv.resize(width);

    forall_operands(it, expr)
    {
      const bvt &op = convert_bv(*it, width);

      if(it==expr.operands().begin())
        bv=op;
      else
      {
        for(std::size_t i=0; i<width; i++)
        {
          if(expr.id()==ID_bitand)
            bv[i]=prop.land(bv[i], op[i]);
          else if(expr.id()==ID_bitor)
            bv[i]=prop.lor(bv[i], op[i]);
          else if(expr.id()==ID_bitxor)
            bv[i]=prop.lxor(bv[i], op[i]);
          else if(expr.id()==ID_bitnand)
            bv[i]=prop.lnand(bv[i], op[i]);
          else if(expr.id()==ID_bitnor)
            bv[i]=prop.lnor(bv[i], op[i]);
          else if(expr.id()==ID_bitxnor)
            bv[i]=prop.lequal(bv[i], op[i]);
          else
            UNIMPLEMENTED;
        }
      }
    }

    return bv;
  }

  UNIMPLEMENTED;
}
