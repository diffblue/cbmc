/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/bitvector_types.h>

bvt boolbvt::convert_div(const div_exprt &expr)
{
  if(expr.type().id()!=ID_unsignedbv &&
     expr.type().id()!=ID_signedbv &&
     expr.type().id()!=ID_fixedbv)
    return conversion_failed(expr);

  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  if(expr.op0().type().id()!=expr.type().id() ||
     expr.op1().type().id()!=expr.type().id())
    return conversion_failed(expr);

  bvt op0=convert_bv(expr.op0());
  bvt op1=convert_bv(expr.op1());

  if(op0.size()!=width ||
     op1.size()!=width)
    throw "convert_div: unexpected operand width";

  bvt res, rem;

  if(expr.type().id()==ID_fixedbv)
  {
    std::size_t fraction_bits=
      to_fixedbv_type(expr.type()).get_fraction_bits();

    bvt zeros;
    zeros.resize(fraction_bits, const_literal(false));

    // add fraction_bits least-significant bits
    op0.insert(op0.begin(), zeros.begin(), zeros.end());
    op1=bv_utils.sign_extension(op1, op1.size()+fraction_bits);

    bv_utils.divider(op0, op1, res, rem, bv_utilst::representationt::SIGNED);

    // cut it down again
    res.resize(width);
  }
  else
  {
    bv_utilst::representationt rep=
      expr.type().id()==ID_signedbv?bv_utilst::representationt::SIGNED:
                                    bv_utilst::representationt::UNSIGNED;

    bv_utils.divider(op0, op1, res, rem, rep);
  }

  return res;
}
