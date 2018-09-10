/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include "boolbv.h"

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

  DATA_INVARIANT(
    expr.op0().type().id() == expr.type().id(),
    "type of the first operand of a modulo operation shall equal the "
    "expression type");

  DATA_INVARIANT(
    expr.op1().type().id() == expr.type().id(),
    "type of the second operand of a modulo operation shall equal the "
    "expression type");

  bv_utilst::representationt rep=
    expr.type().id()==ID_signedbv?bv_utilst::representationt::SIGNED:
                                  bv_utilst::representationt::UNSIGNED;

  const bvt &op0 = convert_bv(expr.op0(), width);
  const bvt &op1 = convert_bv(expr.op1(), width);

  bvt res, rem;

  bv_utils.divider(op0, op1, res, rem, rep);

  return rem;
}
