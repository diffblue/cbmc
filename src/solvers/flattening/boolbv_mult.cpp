/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_types.h>

#include "boolbv.h"

#include "../floatbv/float_utils.h"

/*******************************************************************\

Function: boolbvt::convert_mult

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_mult(const exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());
  
  if(width==0)
    return conversion_failed(expr, bv);

  bv.resize(width);

  const exprt::operandst &operands=expr.operands();
  if(operands.size()==0)
    throw "mult without operands";

  const exprt &op0=expr.op0();

  bool no_overflow=expr.id()=="no-overflow-mult";
  
  if(expr.type().id()==ID_fixedbv)
  {
    if(op0.type()!=expr.type())
      throw "multiplication with mixed types";
    
    bv=convert_bv(op0);

    if(bv.size()!=width)
      throw "convert_mult: unexpected operand width";

    unsigned fraction_bits=
      to_fixedbv_type(expr.type()).get_fraction_bits();
             
    // do a sign extension by fraction_bits bits
    bv=bv_utils.sign_extension(bv, bv.size()+fraction_bits);
      
    for(exprt::operandst::const_iterator it=operands.begin()+1;
        it!=operands.end(); it++)
    {
      if(it->type()!=expr.type())
        throw "multiplication with mixed types";

      bvt op=convert_bv(*it);

      if(op.size()!=width)
        throw "convert_mult: unexpected operand width";

      op=bv_utils.sign_extension(op, bv.size());

      bv=bv_utils.signed_multiplier(bv, op);
    }
    
    // cut it down again
    bv.erase(bv.begin(), bv.begin()+fraction_bits);

    return;
  }
  else if(expr.type().id()==ID_floatbv)
  {
    if(op0.type()!=expr.type())
      throw "multiplication with mixed types";
    
    bv=convert_bv(op0);

    if(bv.size()!=width)
      throw "convert_mult: unexpected operand width";

    float_utilst float_utils(prop);
    float_utils.spec=to_floatbv_type(expr.type());

    for(exprt::operandst::const_iterator it=operands.begin()+1;
        it!=operands.end(); it++)
    {
      if(it->type()!=expr.type())
        throw "multiplication with mixed types";

      const bvt &op=convert_bv(*it);

      if(op.size()!=width)
        throw "convert_mult: unexpected operand width";

      bv=float_utils.mul(bv, op);
    }
    
    return;
  }
  else if(expr.type().id()==ID_unsignedbv ||
          expr.type().id()==ID_signedbv)
  {
    if(op0.type()!=expr.type())
      throw "multiplication with mixed types";
      
    bv_utilst::representationt rep=
      expr.type().id()==ID_signedbv?bv_utilst::SIGNED:
                                    bv_utilst::UNSIGNED;
    
    bv=convert_bv(op0);

    if(bv.size()!=width)
      throw "convert_mult: unexpected operand width";
      
    for(exprt::operandst::const_iterator it=operands.begin()+1;
        it!=operands.end(); it++)
    {
      if(it->type()!=expr.type())
        throw "multiplication with mixed types";

      const bvt &op=convert_bv(*it);

      if(op.size()!=width)
        throw "convert_mult: unexpected operand width";

      if(no_overflow)
        bv=bv_utils.multiplier_no_overflow(bv, op, rep);
      else
        bv=bv_utils.multiplier(bv, op, rep);
    }    

    return;
  }
  
  conversion_failed(expr, bv);
}
