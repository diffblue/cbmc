/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/std_types.h>

bvt boolbvt::convert_mult(const exprt &expr)
{
  const std::size_t width = boolbv_width(expr.type());
  if(width==0)
    return conversion_failed(expr);
  bvt bv;
  bv.resize(width);

  const exprt::operandst &operands=expr.operands();
  DATA_INVARIANT(!operands.empty(), "mult must have operands");
  const exprt &op0=expr.op0();
  const bool no_overflow = expr.id() == "no-overflow-mult";

  if(expr.type().id()==ID_fixedbv)
  {
    DATA_INVARIANT(op0.type() == expr.type(), "multiplication with mixed types");
    bv=convert_bv(op0);

    DATA_INVARIANT(bv.size() == width, "convert_mult: unexpected operand width");
    const std::size_t fraction_bits =
      to_fixedbv_type(expr.type()).get_fraction_bits();

    for(exprt::operandst::const_iterator it=operands.begin()+1;
        it!=operands.end(); it++)
    {
      DATA_INVARIANT(
        it->type() == expr.type(),
        "multiplication should have uniform operand types");

      // do a sign extension by fraction_bits bits
      bv=bv_utils.sign_extension(bv, bv.size()+fraction_bits);
      bvt op=convert_bv(*it);

      INVARIANT(op.size() == width, "convert_mult: unexpected operand width");
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
    DATA_INVARIANT(
      op0.type() == expr.type(), "multiplication with mixed types");
    bv_utilst::representationt rep=
      expr.type().id()==ID_signedbv?bv_utilst::representationt::SIGNED:
                                    bv_utilst::representationt::UNSIGNED;

    bv=convert_bv(op0);
    INVARIANT(bv.size() == width, "convert_mult: unexpected operand width");
    for(exprt::operandst::const_iterator it=operands.begin()+1;
        it!=operands.end(); it++)
    {
      INVARIANT(it->type() == expr.type(), "multiplication with mixed types");
      const bvt &op=convert_bv(*it);
      CHECK_RETURN(op.size() == width);

      bv = no_overflow ? bv_utils.multiplier_no_overflow(bv, op, rep)
                       : bv_utils.multiplier(bv, op, rep);
    }
    return bv;
  }
  return conversion_failed(expr);
}
