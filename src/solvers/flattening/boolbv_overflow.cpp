/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/invariant.h>

#include "boolbv.h"

static bvt mult_overflow_result(
  propt &prop,
  const bvt &bv0,
  const bvt &bv1,
  bv_utilst::representationt rep)
{
  bv_utilst bv_utils{prop};

  std::size_t old_size = bv0.size();
  std::size_t new_size = old_size * 2;

  // sign/zero extension
  const bvt &bv0_extended = bv_utils.extension(bv0, new_size, rep);
  const bvt &bv1_extended = bv_utils.extension(bv1, new_size, rep);

  bvt result_extended = bv_utils.multiplier(bv0_extended, bv1_extended, rep);
  bvt bv{result_extended.begin(), result_extended.begin() + old_size};
  bvt bv_overflow{result_extended.begin() + old_size, result_extended.end()};

  if(rep == bv_utilst::representationt::UNSIGNED)
  {
    bv.push_back(prop.lor(bv_overflow));
  }
  else
  {
    // get top result bits, plus one more
    bv_overflow.push_back(bv.back());

    // these need to be either all 1's or all 0's
    literalt all_one = prop.land(bv_overflow);
    literalt all_zero = !prop.lor(bv_overflow);
    bv.push_back(!prop.lor(all_one, all_zero));
  }

  return bv;
}

static bvt shl_overflow_result(
  propt &prop,
  const bvt &bv0,
  const bvt &bv1,
  bv_utilst::representationt rep0,
  bv_utilst::representationt rep1)
{
  bv_utilst bv_utils{prop};

  std::size_t old_size = bv0.size();
  std::size_t new_size = old_size * 2;

  bvt result_extended = bv_utils.shift(
    bv_utils.extension(bv0, new_size, rep0),
    bv_utilst::shiftt::SHIFT_LEFT,
    bv1);
  bvt bv{result_extended.begin(), result_extended.begin() + old_size};
  bvt bv_overflow{result_extended.begin() + old_size, result_extended.end()};

  // a negative shift is undefined; yet this isn't an overflow
  literalt neg_shift = rep1 == bv_utilst::representationt::UNSIGNED
                         ? const_literal(false)
                         : bv_utils.sign_bit(bv1);

  // an undefined shift of a non-zero value always results in overflow
  std::size_t cmp_width = std::max(bv1.size(), address_bits(old_size) + 1);
  literalt undef = bv_utils.rel(
    bv_utils.extension(bv1, cmp_width, rep1),
    ID_gt,
    bv_utils.build_constant(old_size, cmp_width),
    rep1);

  if(rep0 == bv_utilst::representationt::UNSIGNED)
  {
    // one of the top bits is non-zero
    bv.push_back(prop.lor(bv_overflow));
  }
  else
  {
    // get top result bits, plus one more
    bv_overflow.push_back(bv.back());

    // the sign bit has changed
    literalt sign_change =
      !prop.lequal(bv_utils.sign_bit(bv0), bv_utils.sign_bit(bv));

    // these need to be either all 1's or all 0's
    literalt all_one = prop.land(bv_overflow);
    literalt all_zero = !prop.lor(bv_overflow);

    bv.push_back(prop.lor(sign_change, !prop.lor(all_one, all_zero)));
  }

  // a negative shift isn't an overflow; else check the conditions built
  // above
  bv.back() =
    prop.land(!neg_shift, prop.lselect(undef, prop.lor(bv0), bv.back()));

  return bv;
}

literalt boolbvt::convert_binary_overflow(const binary_overflow_exprt &expr)
{
  const bvt &bv0 = convert_bv(expr.lhs());
  const bvt &bv1 = convert_bv(
    expr.rhs(),
    can_cast_expr<mult_overflow_exprt>(expr)
      ? optionalt<std::size_t>{bv0.size()}
      : nullopt);

  const bv_utilst::representationt rep =
    can_cast_type<signedbv_typet>(expr.lhs().type())
      ? bv_utilst::representationt::SIGNED
      : bv_utilst::representationt::UNSIGNED;

  if(
    const auto plus_overflow = expr_try_dynamic_cast<plus_overflow_exprt>(expr))
  {
    if(bv0.size() != bv1.size())
      return SUB::convert_rest(expr);

    return bv_utils.overflow_add(bv0, bv1, rep);
  }
  if(const auto minus = expr_try_dynamic_cast<minus_overflow_exprt>(expr))
  {
    if(bv0.size() != bv1.size())
      return SUB::convert_rest(expr);

    return bv_utils.overflow_sub(bv0, bv1, rep);
  }
  else if(
    const auto mult_overflow = expr_try_dynamic_cast<mult_overflow_exprt>(expr))
  {
    if(
      !can_cast_type<unsignedbv_typet>(expr.lhs().type()) &&
      !can_cast_type<signedbv_typet>(expr.lhs().type()))
    {
      return SUB::convert_rest(expr);
    }

    DATA_INVARIANT(
      mult_overflow->lhs().type() == mult_overflow->rhs().type(),
      "operands of overflow_mult expression shall have same type");

    DATA_INVARIANT(!bv0.empty(), "zero-sized operand");

    return mult_overflow_result(prop, bv0, bv1, rep).back();
  }
  else if(
    const auto shl_overflow = expr_try_dynamic_cast<shl_overflow_exprt>(expr))
  {
    DATA_INVARIANT(!bv0.empty(), "zero-sized operand");

    return shl_overflow_result(
             prop,
             bv0,
             bv1,
             rep,
             can_cast_type<signedbv_typet>(expr.op1().type())
               ? bv_utilst::representationt::SIGNED
               : bv_utilst::representationt::UNSIGNED)
      .back();
  }

  return SUB::convert_rest(expr);
}

literalt boolbvt::convert_unary_overflow(const unary_overflow_exprt &expr)
{
  if(
    const auto unary_minus_overflow =
      expr_try_dynamic_cast<unary_minus_overflow_exprt>(expr))
  {
    const bvt &bv = convert_bv(unary_minus_overflow->op());

    return bv_utils.overflow_negate(bv);
  }

  return SUB::convert_rest(expr);
}

bvt boolbvt::convert_overflow_result(const overflow_result_exprt &expr)
{
  const typet &type = expr.type();
  const std::size_t width = boolbv_width(type);

  if(expr.id() == ID_overflow_result_unary_minus)
  {
    const bvt op_bv = convert_bv(expr.op0());
    bvt bv = bv_utils.negate(op_bv);
    bv.push_back(bv_utils.overflow_negate(op_bv));
    CHECK_RETURN(bv.size() == width);
    return bv;
  }
  else if(expr.operands().size() != 2)
    return conversion_failed(expr);

  const bvt &bv0 = convert_bv(expr.op0());
  const bvt &bv1 = convert_bv(expr.op1());
  CHECK_RETURN(!bv0.empty() && !bv1.empty());

  const bv_utilst::representationt rep =
    can_cast_type<signedbv_typet>(expr.op0().type())
      ? bv_utilst::representationt::SIGNED
      : bv_utilst::representationt::UNSIGNED;

  if(expr.id() == ID_overflow_result_plus)
  {
    CHECK_RETURN(bv0.size() == bv1.size());

    if(rep == bv_utilst::representationt::SIGNED)
    {
      // An overflow occurs if the signs of the two operands are the same
      // and the sign of the sum is the opposite.
      bvt bv = bv_utils.add(bv0, bv1);

      literalt old_sign = bv_utils.sign_bit(bv0);
      literalt sign_the_same = prop.lequal(old_sign, bv_utils.sign_bit(bv1));
      literalt new_sign = bv_utils.sign_bit(bv);
      bv.push_back(prop.land(sign_the_same, prop.lxor(new_sign, old_sign)));

      CHECK_RETURN(bv.size() == width);
      return bv;
    }
    else
    {
      // overflow is simply carry-out
      bvt bv;
      bv.reserve(width);
      literalt carry = const_literal(false);

      for(std::size_t i = 0; i < bv0.size(); i++)
        bv.push_back(bv_utils.full_adder(bv0[i], bv1[i], carry, carry));

      bv.push_back(carry);

      CHECK_RETURN(bv.size() == width);
      return bv;
    }
  }
  else if(expr.id() == ID_overflow_result_minus)
  {
    CHECK_RETURN(bv0.size() == bv1.size());

    if(rep == bv_utilst::representationt::SIGNED)
    {
      bvt bv1_neg = bv_utils.negate(bv1);
      bvt bv = bv_utils.add(bv0, bv1_neg);

      // We special-case x-INT_MIN, which is >=0 if
      // x is negative, always representable, and
      // thus not an overflow.
      literalt op1_is_int_min = bv_utils.is_int_min(bv1);
      literalt op0_is_negative = bv_utils.sign_bit(bv0);

      literalt old_sign = bv_utils.sign_bit(bv0);
      literalt sign_the_same =
        prop.lequal(old_sign, bv_utils.sign_bit(bv1_neg));
      literalt new_sign = bv_utils.sign_bit(bv);
      bv.push_back(prop.lselect(
        op1_is_int_min,
        !op0_is_negative,
        prop.land(sign_the_same, prop.lxor(new_sign, old_sign))));

      CHECK_RETURN(bv.size() == width);
      return bv;
    }
    else if(rep == bv_utilst::representationt::UNSIGNED)
    {
      // overflow is simply _negated_ carry-out
      bvt bv;
      bv.reserve(width);
      literalt carry = const_literal(true);

      for(std::size_t i = 0; i < bv0.size(); i++)
        bv.push_back(bv_utils.full_adder(bv0[i], !bv1[i], carry, carry));

      bv.push_back(!carry);

      CHECK_RETURN(bv.size() == width);
      return bv;
    }
    else
      UNREACHABLE;
  }
  else if(expr.id() == ID_overflow_result_mult)
  {
    CHECK_RETURN(bv0.size() == bv1.size());

    bvt bv = mult_overflow_result(prop, bv0, bv1, rep);

    CHECK_RETURN(bv.size() == width);
    return bv;
  }
  else if(expr.id() == ID_overflow_result_shl)
  {
    bvt bv = shl_overflow_result(
      prop,
      bv0,
      bv1,
      rep,
      can_cast_type<signedbv_typet>(expr.op1().type())
        ? bv_utilst::representationt::SIGNED
        : bv_utilst::representationt::UNSIGNED);

    CHECK_RETURN(bv.size() == width);
    return bv;
  }

  return conversion_failed(expr);
}
