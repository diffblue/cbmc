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

  DATA_INVARIANT(
    expr.dividend().type().id() == expr.type().id(),
    "type of the dividend of a modulo operation shall equal the "
    "expression type");

  DATA_INVARIANT(
    expr.divisor().type().id() == expr.type().id(),
    "type of the divisor of a modulo operation shall equal the "
    "expression type");

  bv_utilst::representationt rep=
    expr.type().id()==ID_signedbv?bv_utilst::representationt::SIGNED:
                                  bv_utilst::representationt::UNSIGNED;

  const bvt &dividend_bv = convert_bv(expr.dividend(), width);
  const bvt &divisor_bv = convert_bv(expr.divisor(), width);

  bvt res, rem;

  bv_utils.divider(dividend_bv, divisor_bv, res, rem, rep);

  return rem;
}
