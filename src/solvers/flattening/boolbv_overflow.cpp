/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/bitvector_expr.h>
#include <util/invariant.h>

#include "boolbv.h"

literalt boolbvt::convert_overflow(const exprt &expr)
{
  const auto plus_or_minus_conversion =
    [&](
      const binary_overflow_exprt &overflow_expr,
      const std::function<literalt(
        bv_utilst *, const bvt &, const bvt &, bv_utilst::representationt)>
        &bv_util_overflow) {
      const bvt &bv0 = convert_bv(overflow_expr.lhs());
      const bvt &bv1 = convert_bv(overflow_expr.rhs());

      if(bv0.size() != bv1.size())
        return SUB::convert_rest(expr);

      bv_utilst::representationt rep =
        overflow_expr.lhs().type().id() == ID_signedbv
          ? bv_utilst::representationt::SIGNED
          : bv_utilst::representationt::UNSIGNED;

      return bv_util_overflow(&bv_utils, bv0, bv1, rep);
    };
  if(
    const auto plus_overflow = expr_try_dynamic_cast<plus_overflow_exprt>(expr))
  {
    return plus_or_minus_conversion(*plus_overflow, &bv_utilst::overflow_add);
  }
  if(const auto minus = expr_try_dynamic_cast<minus_overflow_exprt>(expr))
  {
    return plus_or_minus_conversion(*minus, &bv_utilst::overflow_sub);
  }
  else if(
    const auto mult_overflow = expr_try_dynamic_cast<mult_overflow_exprt>(expr))
  {
    if(
      mult_overflow->lhs().type().id() != ID_unsignedbv &&
      mult_overflow->lhs().type().id() != ID_signedbv)
      return SUB::convert_rest(expr);

    bvt bv0 = convert_bv(mult_overflow->lhs());
    bvt bv1 = convert_bv(mult_overflow->rhs(), bv0.size());

    bv_utilst::representationt rep =
      mult_overflow->lhs().type().id() == ID_signedbv
        ? bv_utilst::representationt::SIGNED
        : bv_utilst::representationt::UNSIGNED;

    DATA_INVARIANT(
      mult_overflow->lhs().type() == mult_overflow->rhs().type(),
      "operands of overflow_mult expression shall have same type");

    std::size_t old_size=bv0.size();
    std::size_t new_size=old_size*2;

    // sign/zero extension
    bv0=bv_utils.extension(bv0, new_size, rep);
    bv1=bv_utils.extension(bv1, new_size, rep);

    bvt result=bv_utils.multiplier(bv0, bv1, rep);

    if(rep==bv_utilst::representationt::UNSIGNED)
    {
      bvt bv_overflow;
      bv_overflow.reserve(old_size);

      // get top result bits
      for(std::size_t i=old_size; i<result.size(); i++)
        bv_overflow.push_back(result[i]);

      return prop.lor(bv_overflow);
    }
    else
    {
      bvt bv_overflow;
      bv_overflow.reserve(old_size);

      // get top result bits, plus one more
      DATA_INVARIANT(old_size!=0, "zero-size operand");
      for(std::size_t i=old_size-1; i<result.size(); i++)
        bv_overflow.push_back(result[i]);

      // these need to be either all 1's or all 0's
      literalt all_one=prop.land(bv_overflow);
      literalt all_zero=!prop.lor(bv_overflow);
      return !prop.lor(all_one, all_zero);
    }
  }
  else if(
    const auto shl_overflow = expr_try_dynamic_cast<shl_overflow_exprt>(expr))
  {
    const bvt &bv0 = convert_bv(shl_overflow->lhs());
    const bvt &bv1 = convert_bv(shl_overflow->rhs());

    std::size_t old_size = bv0.size();
    std::size_t new_size = old_size * 2;

    bv_utilst::representationt rep =
      shl_overflow->lhs().type().id() == ID_signedbv
        ? bv_utilst::representationt::SIGNED
        : bv_utilst::representationt::UNSIGNED;

    bvt bv_ext=bv_utils.extension(bv0, new_size, rep);

    bvt result=bv_utils.shift(bv_ext, bv_utilst::shiftt::SHIFT_LEFT, bv1);

    // a negative shift is undefined; yet this isn't an overflow
    literalt neg_shift = shl_overflow->lhs().type().id() == ID_unsignedbv
                           ? const_literal(false)
                           : bv1.back(); // sign bit

    // an undefined shift of a non-zero value always results in overflow; the
    // use of unsigned comparision is safe here as we cover the signed negative
    // case via neg_shift
    literalt undef =
      bv_utils.rel(
        bv1,
        ID_gt,
        bv_utils.build_constant(old_size, bv1.size()),
        bv_utilst::representationt::UNSIGNED);

    literalt overflow;

    if(rep == bv_utilst::representationt::UNSIGNED)
    {
      // get top result bits
      result.erase(result.begin(), result.begin() + old_size);

      // one of the top bits is non-zero
      overflow=prop.lor(result);
    }
    else
    {
      // get top result bits plus sign bit
      DATA_INVARIANT(old_size != 0, "zero-size operand");
      result.erase(result.begin(), result.begin() + old_size - 1);

      // the sign bit has changed
      literalt sign_change=!prop.lequal(bv0.back(), result.front());

      // these need to be either all 1's or all 0's
      literalt all_one=prop.land(result);
      literalt all_zero=!prop.lor(result);

      overflow=prop.lor(sign_change, !prop.lor(all_one, all_zero));
    }

    // a negative shift isn't an overflow; else check the conditions built
    // above
    return
      prop.land(!neg_shift, prop.lselect(undef, prop.lor(bv0), overflow));
  }
  else if(expr.id()==ID_overflow_unary_minus)
  {
    const auto &overflow_expr = to_unary_expr(expr);

    const bvt &bv = convert_bv(overflow_expr.op());

    return bv_utils.overflow_negate(bv);
  }

  return SUB::convert_rest(expr);
}
