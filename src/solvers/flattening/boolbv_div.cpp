/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/std_types.h>

bvt boolbvt::convert_div(const div_exprt &div_expr)
{
  if(
    div_expr.type().id() != ID_unsignedbv &&
    div_expr.type().id() != ID_signedbv && div_expr.type().id() != ID_fixedbv)
    return conversion_failed(div_expr);

  std::size_t bv_width = boolbv_width(div_expr.type());

  if(bv_width == 0)
    return conversion_failed(div_expr);

  if(
    div_expr.dividend().type().id() != div_expr.type().id() ||
    div_expr.divisor().type().id() != div_expr.type().id())
    return conversion_failed(div_expr);

  bvt dividend = convert_bv(div_expr.dividend());
  bvt divisor = convert_bv(div_expr.divisor());

  INVARIANT(
    dividend.size() == divisor.size(),
    "bitvectors of the same type should have the same length");

  bvt result, remainder;

  if(div_expr.type().id() == ID_fixedbv)
  {
    std::size_t fraction_bits =
      to_fixedbv_type(div_expr.type()).get_fraction_bits();

    bvt zeros;
    zeros.resize(fraction_bits, const_literal(false));

    // add fraction_bits least-significant bits
    dividend.insert(dividend.begin(), zeros.begin(), zeros.end());
    divisor = bv_utils.sign_extension(divisor, divisor.size() + fraction_bits);

    bv_utils.divider(
      dividend, divisor, result, remainder, bv_utilst::representationt::SIGNED);

    // cut it down again
    result.resize(bv_width);
  }
  else
  {
    bv_utilst::representationt rep = div_expr.type().id() == ID_signedbv
                                       ? bv_utilst::representationt::SIGNED
                                       : bv_utilst::representationt::UNSIGNED;

    bv_utils.divider(dividend, divisor, result, remainder, rep);
  }

  return result;
}
