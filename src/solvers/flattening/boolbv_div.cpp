/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_types.h>

#include "boolbv.h"

#include "../floatbv/float_utils.h"

/*******************************************************************\

Function: boolbvt::convert_div

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_div(const exprt &expr, bvt &bv)
{
  if(expr.type().id()!=ID_unsignedbv &&
     expr.type().id()!=ID_signedbv &&
     expr.type().id()!=ID_fixedbv &&
     expr.type().id()!=ID_floatbv)
    return conversion_failed(expr, bv);

  unsigned width=boolbv_width(expr.type());
  
  if(width==0)
    return conversion_failed(expr, bv);

  if(expr.operands().size()!=2)
    throw "division takes two operands";

  if(expr.op0().type().id()!=expr.type().id() ||
     expr.op1().type().id()!=expr.type().id())
    return conversion_failed(expr, bv);

  bvt op0=convert_bv(expr.op0());
  bvt op1=convert_bv(expr.op1());

  if(op0.size()!=width ||
     op1.size()!=width)
    throw "convert_div: unexpected operand width";

  bvt res, rem;

  if(expr.type().id()==ID_fixedbv)
  {
    unsigned fraction_bits=
      to_fixedbv_type(expr.type()).get_fraction_bits();

    bvt zeros;
    zeros.resize(fraction_bits, const_literal(false));

    // add fraction_bits least-significant bits
    op0.insert(op0.begin(), zeros.begin(), zeros.end());
    op1=bv_utils.sign_extension(op1, op1.size()+fraction_bits);
  
    bv_utils.divider(op0, op1, res, rem, bv_utilst::SIGNED);
    
    // cut it down again
    res.resize(width);
  }
  else if(expr.type().id()==ID_floatbv)
  {
    float_utilst float_utils(prop);
    float_utils.spec=to_floatbv_type(expr.type());
    res=float_utils.div(op0, op1);
  }
  else
  {
    bv_utilst::representationt rep=
      expr.type().id()==ID_signedbv?bv_utilst::SIGNED:
                                   bv_utilst::UNSIGNED;

    bv_utils.divider(op0, op1, res, rem, rep);
  }

  bv=res;
}
