/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_mod

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt boolbvt::convert_mod(const mod_exprt &expr)
{
  #if 0
  // TODO
  if(expr.type().id()==ID_floatbv)
  {
  }
  #endif

  if(expr.type().id()!=ID_unsignedbv &&
     expr.type().id()!=ID_signedbv)
    return conversion_failed(expr);

  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  if(expr.op0().type().id()!=expr.type().id() ||
     expr.op1().type().id()!=expr.type().id())
    throw "mod got mixed-type operands";

  bv_utilst::representationt rep=
    expr.type().id()==ID_signedbv?bv_utilst::SIGNED:
                                  bv_utilst::UNSIGNED;

  const bvt &op0=convert_bv(expr.op0());
  const bvt &op1=convert_bv(expr.op1());

  if(op0.size()!=width ||
     op1.size()!=width)
    throw "convert_mod: unexpected operand width";

  bvt res, rem;

  bv_utils.divider(op0, op1, res, rem, rep);

  return rem;
}
