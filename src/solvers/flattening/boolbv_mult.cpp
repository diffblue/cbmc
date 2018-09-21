/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/std_types.h>

bvt boolbvt::convert_mult(const mult_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  bvt bv;
  bv.resize(width);

  const exprt::operandst &operands=expr.operands();
  DATA_INVARIANT(!operands.empty(), "multiplication must have operands");

  const exprt &op0=expr.op0();

  DATA_INVARIANT(
    op0.type() == expr.type(),
    "multiplication operands should have same type as expression");

  if(expr.type().id()==ID_fixedbv)
  {
    bv = convert_bv(op0, width);

    std::size_t fraction_bits=
      to_fixedbv_type(expr.type()).get_fraction_bits();

    for(exprt::operandst::const_iterator it=operands.begin()+1;
        it!=operands.end(); it++)
    {
      DATA_INVARIANT(
        it->type() == expr.type(),
        "multiplication operands should have same type as expression");

      // do a sign extension by fraction_bits bits
      bv=bv_utils.sign_extension(bv, bv.size()+fraction_bits);

      bvt op = convert_bv(*it, width);

      op=bv_utils.sign_extension(op, bv.size());

      bv=bv_utils.signed_multiplier(bv, op);

      // cut it down again
      bv.erase(bv.begin(), bv.begin()+fraction_bits);
    }

    return bv;
  }
  else if(expr.type().id()==ID_unsignedbv ||
          expr.type().id()==ID_signedbv)
  {
    bv_utilst::representationt rep=
      expr.type().id()==ID_signedbv?bv_utilst::representationt::SIGNED:
                                    bv_utilst::representationt::UNSIGNED;

    bv = convert_bv(op0, width);

    for(exprt::operandst::const_iterator it=operands.begin()+1;
        it!=operands.end(); it++)
    {
      DATA_INVARIANT(
        it->type() == expr.type(),
        "multiplication operands should have same type as expression");

      const bvt &op = convert_bv(*it, width);

      bv = bv_utils.multiplier(bv, op, rep);
    }

    return bv;
  }

  return conversion_failed(expr);
}
