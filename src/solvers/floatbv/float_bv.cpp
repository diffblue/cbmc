/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "float_bv.h"

#include <algorithm>

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/floatbv_expr.h>
#include <util/std_expr.h>

exprt float_bvt::convert(const exprt &expr) const
{
  if(expr.id()==ID_abs)
    return abs(to_abs_expr(expr).op(), get_spec(expr));
  else if(expr.id()==ID_unary_minus)
    return negation(to_unary_minus_expr(expr).op(), get_spec(expr));
  else if(expr.id()==ID_ieee_float_equal)
  {
    const auto &equal_expr = to_ieee_float_equal_expr(expr);
    return is_equal(
      equal_expr.lhs(), equal_expr.rhs(), get_spec(equal_expr.lhs()));
  }
  else if(expr.id()==ID_ieee_float_notequal)
  {
    const auto &notequal_expr = to_ieee_float_notequal_expr(expr);
    return not_exprt(is_equal(
      notequal_expr.lhs(), notequal_expr.rhs(), get_spec(notequal_expr.lhs())));
  }
  else if(expr.id()==ID_floatbv_typecast)
  {
    const auto &floatbv_typecast_expr = to_floatbv_typecast_expr(expr);
    const auto &op = floatbv_typecast_expr.op();
    const typet &src_type = floatbv_typecast_expr.op().type();
    const typet &dest_type = floatbv_typecast_expr.type();
    const auto &rounding_mode = floatbv_typecast_expr.rounding_mode();

    if(dest_type.id()==ID_signedbv &&
       src_type.id()==ID_floatbv) // float -> signed
      return to_signed_integer(
        op,
        to_signedbv_type(dest_type).get_width(),
        rounding_mode,
        get_spec(op));
    else if(dest_type.id()==ID_unsignedbv &&
            src_type.id()==ID_floatbv) // float -> unsigned
      return to_unsigned_integer(
        op,
        to_unsignedbv_type(dest_type).get_width(),
        rounding_mode,
        get_spec(op));
    else if(src_type.id()==ID_signedbv &&
            dest_type.id()==ID_floatbv) // signed -> float
      return from_signed_integer(op, rounding_mode, get_spec(expr));
    else if(src_type.id()==ID_unsignedbv &&
            dest_type.id()==ID_floatbv) // unsigned -> float
    {
      return from_unsigned_integer(op, rounding_mode, get_spec(expr));
    }
    else if(dest_type.id()==ID_floatbv &&
            src_type.id()==ID_floatbv) // float -> float
    {
      return conversion(op, rounding_mode, get_spec(op), get_spec(expr));
    }
    else
      return nil_exprt();
  }
  else if(
    expr.id() == ID_typecast && expr.is_boolean() &&
    to_typecast_expr(expr).op().type().id() == ID_floatbv) // float -> bool
  {
    return not_exprt(is_zero(to_typecast_expr(expr).op()));
  }
  else if(
    expr.id() == ID_typecast && expr.type().id() == ID_bv &&
    to_typecast_expr(expr).op().type().id() == ID_floatbv) // float -> raw bv
  {
    const typecast_exprt &tc = to_typecast_expr(expr);
    const bitvector_typet &dest_type = to_bitvector_type(expr.type());
    const floatbv_typet &src_type = to_floatbv_type(tc.op().type());
    if(
      dest_type.get_width() != src_type.get_width() ||
      dest_type.get_width() == 0)
    {
      return nil_exprt{};
    }

    return extractbits_exprt{to_typecast_expr(expr).op(), 0, dest_type};
  }
  else if(expr.id()==ID_floatbv_plus)
  {
    const auto &float_expr = to_ieee_float_op_expr(expr);
    return add_sub(
      false,
      float_expr.lhs(),
      float_expr.rhs(),
      float_expr.rounding_mode(),
      get_spec(expr));
  }
  else if(expr.id()==ID_floatbv_minus)
  {
    const auto &float_expr = to_ieee_float_op_expr(expr);
    return add_sub(
      true,
      float_expr.lhs(),
      float_expr.rhs(),
      float_expr.rounding_mode(),
      get_spec(expr));
  }
  else if(expr.id()==ID_floatbv_mult)
  {
    const auto &float_expr = to_ieee_float_op_expr(expr);
    return mul(
      float_expr.lhs(),
      float_expr.rhs(),
      float_expr.rounding_mode(),
      get_spec(expr));
  }
  else if(expr.id()==ID_floatbv_div)
  {
    const auto &float_expr = to_ieee_float_op_expr(expr);
    return div(
      float_expr.lhs(),
      float_expr.rhs(),
      float_expr.rounding_mode(),
      get_spec(expr));
  }
  else if(expr.id() == ID_floatbv_fma)
  {
    const auto &fma_expr = to_floatbv_fma_expr(expr);
    const ieee_float_spect spec{to_floatbv_type(fma_expr.type())};
    return fma(
      fma_expr.op_multiply_lhs(),
      fma_expr.op_multiply_rhs(),
      fma_expr.op_add(),
      fma_expr.rounding_mode(),
      spec);
  }
  else if(expr.id()==ID_isnan)
  {
    const auto &op = to_unary_expr(expr).op();
    return isnan(op, get_spec(op));
  }
  else if(expr.id()==ID_isfinite)
  {
    const auto &op = to_unary_expr(expr).op();
    return isfinite(op, get_spec(op));
  }
  else if(expr.id()==ID_isinf)
  {
    const auto &op = to_unary_expr(expr).op();
    return isinf(op, get_spec(op));
  }
  else if(expr.id()==ID_isnormal)
  {
    const auto &op = to_unary_expr(expr).op();
    return isnormal(op, get_spec(op));
  }
  else if(expr.id()==ID_lt)
  {
    const auto &rel_expr = to_binary_relation_expr(expr);
    return relation(
      rel_expr.lhs(), relt::LT, rel_expr.rhs(), get_spec(rel_expr.lhs()));
  }
  else if(expr.id()==ID_gt)
  {
    const auto &rel_expr = to_binary_relation_expr(expr);
    return relation(
      rel_expr.lhs(), relt::GT, rel_expr.rhs(), get_spec(rel_expr.lhs()));
  }
  else if(expr.id()==ID_le)
  {
    const auto &rel_expr = to_binary_relation_expr(expr);
    return relation(
      rel_expr.lhs(), relt::LE, rel_expr.rhs(), get_spec(rel_expr.lhs()));
  }
  else if(expr.id()==ID_ge)
  {
    const auto &rel_expr = to_binary_relation_expr(expr);
    return relation(
      rel_expr.lhs(), relt::GE, rel_expr.rhs(), get_spec(rel_expr.lhs()));
  }
  else if(expr.id()==ID_sign)
    return sign_bit(to_unary_expr(expr).op());

  return nil_exprt();
}

ieee_float_spect float_bvt::get_spec(const exprt &expr)
{
  const floatbv_typet &type=to_floatbv_type(expr.type());
  return ieee_float_spect(type);
}

exprt float_bvt::abs(const exprt &op, const ieee_float_spect &spec)
{
  // we mask away the sign bit, which is the most significant bit
  const mp_integer v = power(2, spec.width() - 1) - 1;

  const constant_exprt mask(integer2bvrep(v, spec.width()), op.type());

  return bitand_exprt(op, mask);
}

exprt float_bvt::negation(const exprt &op, const ieee_float_spect &spec)
{
  // we flip the sign bit with an xor
  const mp_integer v = power(2, spec.width() - 1);

  constant_exprt mask(integer2bvrep(v, spec.width()), op.type());

  return bitxor_exprt(op, mask);
}

exprt float_bvt::is_equal(
  const exprt &src0,
  const exprt &src1,
  const ieee_float_spect &spec)
{
  // special cases: -0 and 0 are equal
  const exprt is_zero0 = is_zero(src0);
  const exprt is_zero1 = is_zero(src1);
  const and_exprt both_zero(is_zero0, is_zero1);

  // NaN compares to nothing
  exprt isnan0=isnan(src0, spec);
  exprt isnan1=isnan(src1, spec);
  const or_exprt nan(isnan0, isnan1);

  const equal_exprt bitwise_equal(src0, src1);

  return and_exprt(
    or_exprt(bitwise_equal, both_zero),
    not_exprt(nan));
}

exprt float_bvt::is_zero(const exprt &src)
{
  // we mask away the sign bit, which is the most significant bit
  const floatbv_typet &type=to_floatbv_type(src.type());
  std::size_t width=type.get_width();

  const mp_integer v = power(2, width - 1) - 1;

  constant_exprt mask(integer2bvrep(v, width), src.type());

  ieee_float_valuet z(type);
  z.make_zero();

  return equal_exprt(bitand_exprt(src, mask), z.to_expr());
}

exprt float_bvt::exponent_all_ones(
  const exprt &src,
  const ieee_float_spect &spec)
{
  exprt exponent=get_exponent(src, spec);
  exprt all_ones=to_unsignedbv_type(exponent.type()).largest_expr();
  return equal_exprt(exponent, all_ones);
}

exprt float_bvt::exponent_all_zeros(
  const exprt &src,
  const ieee_float_spect &spec)
{
  exprt exponent=get_exponent(src, spec);
  exprt all_zeros=to_unsignedbv_type(exponent.type()).zero_expr();
  return equal_exprt(exponent, all_zeros);
}

exprt float_bvt::fraction_all_zeros(
  const exprt &src,
  const ieee_float_spect &spec)
{
  // does not include hidden bit
  exprt fraction=get_fraction(src, spec);
  exprt all_zeros=to_unsignedbv_type(fraction.type()).zero_expr();
  return equal_exprt(fraction, all_zeros);
}

void float_bvt::rounding_mode_bitst::get(const exprt &rm)
{
  exprt round_to_even_const=from_integer(ieee_floatt::ROUND_TO_EVEN, rm.type());
  exprt round_to_plus_inf_const=
    from_integer(ieee_floatt::ROUND_TO_PLUS_INF, rm.type());
  exprt round_to_minus_inf_const=
    from_integer(ieee_floatt::ROUND_TO_MINUS_INF, rm.type());
  exprt round_to_zero_const=from_integer(ieee_floatt::ROUND_TO_ZERO, rm.type());
  exprt round_to_away_const =
    from_integer(ieee_floatt::ROUND_TO_AWAY, rm.type());

  round_to_even=equal_exprt(rm, round_to_even_const);
  round_to_plus_inf=equal_exprt(rm, round_to_plus_inf_const);
  round_to_minus_inf=equal_exprt(rm, round_to_minus_inf_const);
  round_to_zero=equal_exprt(rm, round_to_zero_const);
  round_to_away = equal_exprt(rm, round_to_away_const);
}

exprt float_bvt::sign_bit(const exprt &op)
{
  const bitvector_typet &bv_type=to_bitvector_type(op.type());
  std::size_t width=bv_type.get_width();
  return extractbit_exprt(op, width-1);
}

exprt float_bvt::from_signed_integer(
  const exprt &src,
  const exprt &rm,
  const ieee_float_spect &spec) const
{
  std::size_t src_width=to_signedbv_type(src.type()).get_width();

  unbiased_floatt result;

  // we need to adjust for negative integers
  result.sign=sign_bit(src);

  result.fraction=
    typecast_exprt(abs_exprt(src), unsignedbv_typet(src_width));

  // build an exponent (unbiased) -- this is signed!
  result.exponent=
    from_integer(
      src_width-1,
      signedbv_typet(address_bits(src_width - 1) + 1));

  return rounder(result, rm, spec);
}

exprt float_bvt::from_unsigned_integer(
  const exprt &src,
  const exprt &rm,
  const ieee_float_spect &spec) const
{
  unbiased_floatt result;

  result.fraction=src;

  std::size_t src_width=to_unsignedbv_type(src.type()).get_width();

  // build an exponent (unbiased) -- this is signed!
  result.exponent=
    from_integer(
      src_width-1,
      signedbv_typet(address_bits(src_width - 1) + 1));

  result.sign=false_exprt();

  return rounder(result, rm, spec);
}

exprt float_bvt::to_signed_integer(
  const exprt &src,
  std::size_t dest_width,
  const exprt &rm,
  const ieee_float_spect &spec)
{
  return to_integer(src, dest_width, true, rm, spec);
}

exprt float_bvt::to_unsigned_integer(
  const exprt &src,
  std::size_t dest_width,
  const exprt &rm,
  const ieee_float_spect &spec)
{
  return to_integer(src, dest_width, false, rm, spec);
}

exprt float_bvt::to_integer(
  const exprt &src,
  std::size_t dest_width,
  bool is_signed,
  const exprt &rm,
  const ieee_float_spect &spec)
{
  // Keep in sync with float_utilst::to_integer — the body below is a
  // line-for-line translation of that function between the exprt and
  // literalt/bvt APIs.

  const unbiased_floatt unpacked=unpack(src, spec);

  rounding_mode_bitst rounding_mode_bits(rm);

  // Right now hard-wired to round-to-zero, which is
  // the usual case in ANSI-C.

  const std::size_t fraction_width =
    to_unsignedbv_type(unpacked.fraction.type()).get_width();

  // Extend the fraction to dest_width if needed, padding with zeros
  // at the LSB end (like float_utilst does).
  exprt fraction = unpacked.fraction;
  std::size_t effective_width = fraction_width;

  if(dest_width > fraction_width)
  {
    effective_width = dest_width;
    fraction = concatenation_exprt(
      fraction,
      from_integer(0, unsignedbv_typet(dest_width - fraction_width)),
      unsignedbv_typet(effective_width));
  }

  // if the exponent is positive, shift right by (effective_width - 1) minus
  // the exponent. The shift distance is built in a signed type wide enough to
  // hold both `effective_width - 1` and the (sign-extended) exponent, so it
  // does not wrap for wide destination types -- e.g. a narrow source such as
  // _Float16 (spec.e = 5) converted to a 64-bit integer. Keep in sync with
  // float_utilst::to_integer.
  const signedbv_typet distance_type(std::max(
    static_cast<std::size_t>(spec.e), address_bits(effective_width) + 1));
  const exprt offset = from_integer(effective_width - 1, distance_type);
  const minus_exprt distance(
    offset, typecast_exprt(unpacked.exponent, distance_type));
  const lshr_exprt shift_result(fraction, distance);

  // if the exponent is negative, we have zero anyways
  exprt result=shift_result;
  const sign_exprt exponent_sign(unpacked.exponent);

  result=
    if_exprt(exponent_sign, from_integer(0, result.type()), result);

  // chop out the right number of bits from the result
  typet result_type=
    is_signed?static_cast<typet>(signedbv_typet(dest_width)):
              static_cast<typet>(unsignedbv_typet(dest_width));

  result=typecast_exprt(result, result_type);

  // if signed, apply sign.
  if(is_signed)
  {
    result=if_exprt(
      unpacked.sign, unary_minus_exprt(result), result);
  }
  else
  {
    // It's unclear what the behaviour for negative floats
    // to integer shall be.
  }

  return result;
}

exprt float_bvt::conversion(
  const exprt &src,
  const exprt &rm,
  const ieee_float_spect &src_spec,
  const ieee_float_spect &dest_spec) const
{
  // Catch the special case in which we extend,
  // e.g. single to double.
  // In this case, rounding can be avoided,
  // but a denormal number may be come normal.
  // Be careful to exclude the difficult case
  // when denormalised numbers in the old format
  // can be converted to denormalised numbers in the
  // new format.  Note that this is rare and will only
  // happen with very non-standard formats.

  int sourceSmallestNormalExponent = -((1 << (src_spec.e - 1)) - 1);
  int sourceSmallestDenormalExponent =
    sourceSmallestNormalExponent - src_spec.f;

  // Using the fact that f doesn't include the hidden bit

  int destSmallestNormalExponent = -((1 << (dest_spec.e - 1)) - 1);

  if(dest_spec.e>=src_spec.e &&
     dest_spec.f>=src_spec.f &&
     !(sourceSmallestDenormalExponent < destSmallestNormalExponent))
  {
    unbiased_floatt unpacked_src=unpack(src, src_spec);
    unbiased_floatt result;

    // the fraction gets zero-padded
    std::size_t padding=dest_spec.f-src_spec.f;
    result.fraction=
      concatenation_exprt(
        unpacked_src.fraction,
        from_integer(0, unsignedbv_typet(padding)),
        unsignedbv_typet(dest_spec.f+1));

    // the exponent gets sign-extended
    INVARIANT(
      unpacked_src.exponent.type().id() == ID_signedbv,
      "the exponent needs to have a signed type");
    result.exponent=
      typecast_exprt(unpacked_src.exponent, signedbv_typet(dest_spec.e));

    // if the number was denormal and is normal in the new format,
    // normalise it!
    if(dest_spec.e > src_spec.e)
    {
      normalization_shift(result.fraction, result.exponent);
      // normalization_shift unconditionally extends the exponent size to avoid
      // arithmetic overflow, but this cannot have happened here as the exponent
      // had already been extended to dest_spec's size
      result.exponent =
        typecast_exprt(result.exponent, signedbv_typet(dest_spec.e));
    }

    // the flags get copied
    result.sign=unpacked_src.sign;
    result.NaN=unpacked_src.NaN;
    result.infinity=unpacked_src.infinity;

    // no rounding needed!
    return pack(bias(result, dest_spec), dest_spec);
  }
  else
  {
    // we actually need to round
    unbiased_floatt result=unpack(src, src_spec);
    return rounder(result, rm, dest_spec);
  }
}

exprt float_bvt::isnormal(
  const exprt &src,
  const ieee_float_spect &spec)
{
  return and_exprt(
           not_exprt(exponent_all_zeros(src, spec)),
           not_exprt(exponent_all_ones(src, spec)));
}

/// Subtracts the exponents
exprt float_bvt::subtract_exponents(
  const unbiased_floatt &src1,
  const unbiased_floatt &src2)
{
  // extend both by one bit
  std::size_t old_width1=to_signedbv_type(src1.exponent.type()).get_width();
  std::size_t old_width2=to_signedbv_type(src2.exponent.type()).get_width();
  PRECONDITION(old_width1 == old_width2);

  const typecast_exprt extended_exponent1(
    src1.exponent, signedbv_typet(old_width1 + 1));

  const typecast_exprt extended_exponent2(
    src2.exponent, signedbv_typet(old_width2 + 1));

  // compute shift distance (here is the subtraction)
  return minus_exprt(extended_exponent1, extended_exponent2);
}

exprt float_bvt::add_sub(
  bool subtract,
  const exprt &op0,
  const exprt &op1,
  const exprt &rm,
  const ieee_float_spect &spec) const
{
  unbiased_floatt unpacked1=unpack(op0, spec);
  unbiased_floatt unpacked2=unpack(op1, spec);

  // subtract?
  if(subtract)
    unpacked2.sign=not_exprt(unpacked2.sign);

  // figure out which operand has the bigger exponent
  const exprt exponent_difference=subtract_exponents(unpacked1, unpacked2);
  const sign_exprt src2_bigger(exponent_difference);

  const exprt bigger_exponent=
    if_exprt(src2_bigger, unpacked2.exponent, unpacked1.exponent);

  // swap fractions as needed
  const exprt new_fraction1=
    if_exprt(src2_bigger, unpacked2.fraction, unpacked1.fraction);

  const exprt new_fraction2=
    if_exprt(src2_bigger, unpacked1.fraction, unpacked2.fraction);

  // compute distance
  const exprt distance=
    typecast_exprt(abs_exprt(exponent_difference), unsignedbv_typet(spec.e));

  // limit the distance: shifting more than f+3 bits is unnecessary
  const exprt limited_dist=limit_distance(distance, spec.f+3);

  // pad fractions with 3 zeros from below
  exprt three_zeros=from_integer(0, unsignedbv_typet(3));
  // add 4 to spec.f because unpacked new_fraction has the hidden bit
  const exprt fraction1_padded=
    concatenation_exprt(new_fraction1, three_zeros, unsignedbv_typet(spec.f+4));
  const exprt fraction2_padded=
    concatenation_exprt(new_fraction2, three_zeros, unsignedbv_typet(spec.f+4));

  // shift new_fraction2
  exprt sticky_bit;
  const exprt fraction1_shifted=fraction1_padded;
  const exprt fraction2_shifted=sticky_right_shift(
    fraction2_padded, limited_dist, sticky_bit);

  // sticky bit: 'or' of the bits lost by the right-shift
  const bitor_exprt fraction2_stickied(
    fraction2_shifted,
    concatenation_exprt(
      from_integer(0, unsignedbv_typet(spec.f + 3)),
      sticky_bit,
      fraction2_shifted.type()));

  // need to have two extra fraction bits for addition and rounding
  const exprt fraction1_ext=
    typecast_exprt(fraction1_shifted, unsignedbv_typet(spec.f+4+2));
  const exprt fraction2_ext=
    typecast_exprt(fraction2_stickied, unsignedbv_typet(spec.f+4+2));

  unbiased_floatt result;

  // now add/sub them
  const notequal_exprt subtract_lit(unpacked1.sign, unpacked2.sign);

  result.fraction=
    if_exprt(subtract_lit,
      minus_exprt(fraction1_ext, fraction2_ext),
      plus_exprt(fraction1_ext, fraction2_ext));

  // sign of result
  std::size_t width=to_bitvector_type(result.fraction.type()).get_width();
  const sign_exprt fraction_sign(
    typecast_exprt(result.fraction, signedbv_typet(width)));
  result.fraction=
    typecast_exprt(
      abs_exprt(typecast_exprt(result.fraction, signedbv_typet(width))),
      unsignedbv_typet(width));

  result.exponent=bigger_exponent;

  // adjust the exponent for the fact that we added two bits to the fraction
  result.exponent=
    plus_exprt(typecast_exprt(result.exponent, signedbv_typet(spec.e+1)),
               from_integer(2, signedbv_typet(spec.e+1)));

  // NaN?
  result.NaN=or_exprt(
      and_exprt(and_exprt(unpacked1.infinity, unpacked2.infinity),
                notequal_exprt(unpacked1.sign, unpacked2.sign)),
      or_exprt(unpacked1.NaN, unpacked2.NaN));

  // infinity?
  result.infinity=and_exprt(
      not_exprt(result.NaN),
      or_exprt(unpacked1.infinity, unpacked2.infinity));

  // zero?
  // Note that:
  //  1. The zero flag isn't used apart from in divide and
  //     is only set on unpack
  //  2. Subnormals mean that addition or subtraction can't round to 0,
  //     thus we can perform this test now
  //  3. The rules for sign are different for zero
  result.zero=
    and_exprt(
      not_exprt(or_exprt(result.infinity, result.NaN)),
      equal_exprt(
        result.fraction,
        from_integer(0, result.fraction.type())));

  // sign
  const notequal_exprt add_sub_sign(
    if_exprt(src2_bigger, unpacked2.sign, unpacked1.sign), fraction_sign);

  const if_exprt infinity_sign(
    unpacked1.infinity, unpacked1.sign, unpacked2.sign);

  #if 1
  rounding_mode_bitst rounding_mode_bits(rm);

  const if_exprt zero_sign(
    rounding_mode_bits.round_to_minus_inf,
    or_exprt(unpacked1.sign, unpacked2.sign),
    and_exprt(unpacked1.sign, unpacked2.sign));

  result.sign=if_exprt(
    result.infinity,
    infinity_sign,
    if_exprt(result.zero,
             zero_sign,
             add_sub_sign));
  #else
  result.sign=if_exprt(
    result.infinity,
    infinity_sign,
    add_sub_sign);
  #endif

  return rounder(result, rm, spec);
}

/// Limits the shift distance
exprt float_bvt::limit_distance(
  const exprt &dist,
  mp_integer limit)
{
  std::size_t nb_bits = address_bits(limit);
  std::size_t dist_width=to_unsignedbv_type(dist.type()).get_width();

  if(dist_width<=nb_bits)
    return dist;

  const extractbits_exprt upper_bits(
    dist, nb_bits, unsignedbv_typet(dist_width - nb_bits));
  const equal_exprt upper_bits_zero(
    upper_bits, from_integer(0, upper_bits.type()));

  const extractbits_exprt lower_bits(dist, 0, unsignedbv_typet(nb_bits));

  return if_exprt(
    upper_bits_zero,
    lower_bits,
    unsignedbv_typet(nb_bits).largest_expr());
}

exprt float_bvt::mul(
  const exprt &src1,
  const exprt &src2,
  const exprt &rm,
  const ieee_float_spect &spec) const
{
  // unpack
  const unbiased_floatt unpacked1=unpack(src1, spec);
  const unbiased_floatt unpacked2=unpack(src2, spec);

  // zero-extend the fractions (unpacked fraction has the hidden bit)
  typet new_fraction_type=unsignedbv_typet((spec.f+1)*2);
  const exprt fraction1 =
    zero_extend_exprt{unpacked1.fraction, new_fraction_type};
  const exprt fraction2 =
    zero_extend_exprt{unpacked2.fraction, new_fraction_type};

  // multiply the fractions
  unbiased_floatt result;
  result.fraction=mult_exprt(fraction1, fraction2);

  // extend exponents to account for overflow
  // add two bits, as we do extra arithmetic on it later
  typet new_exponent_type=signedbv_typet(spec.e+2);
  const exprt exponent1=typecast_exprt(unpacked1.exponent, new_exponent_type);
  const exprt exponent2=typecast_exprt(unpacked2.exponent, new_exponent_type);

  const plus_exprt added_exponent(exponent1, exponent2);

  // Adjust exponent; we are thowing in an extra fraction bit,
  // it has been extended above.
  result.exponent=
    plus_exprt(added_exponent, from_integer(1, new_exponent_type));

  // new sign
  result.sign=notequal_exprt(unpacked1.sign, unpacked2.sign);

  // infinity?
  result.infinity=or_exprt(unpacked1.infinity, unpacked2.infinity);

  // NaN?
  result.NaN = disjunction(
    {isnan(src1, spec),
     isnan(src2, spec),
     // infinity * 0 is NaN!
     and_exprt(unpacked1.zero, unpacked2.infinity),
     and_exprt(unpacked2.zero, unpacked1.infinity)});

  return rounder(result, rm, spec);
}

exprt float_bvt::div(
  const exprt &src1,
  const exprt &src2,
  const exprt &rm,
  const ieee_float_spect &spec) const
{
  // unpack
  const unbiased_floatt unpacked1=unpack(src1, spec);
  const unbiased_floatt unpacked2=unpack(src2, spec);

  std::size_t fraction_width=
    to_unsignedbv_type(unpacked1.fraction.type()).get_width();
  std::size_t div_width=fraction_width*2+1;

  // pad fraction1 with zeros
  const concatenation_exprt fraction1(
    unpacked1.fraction,
    from_integer(0, unsignedbv_typet(div_width - fraction_width)),
    unsignedbv_typet(div_width));

  // zero-extend fraction2 to match fraction1
  const zero_extend_exprt fraction2{unpacked2.fraction, fraction1.type()};

  // divide fractions
  unbiased_floatt result;
  exprt rem;

  // the below should be merged somehow
  result.fraction=div_exprt(fraction1, fraction2);
  rem=mod_exprt(fraction1, fraction2);

  // is there a remainder?
  const notequal_exprt have_remainder(rem, from_integer(0, rem.type()));

  // we throw this into the result, as least-significant bit,
  // to get the right rounding decision
  result.fraction=
    concatenation_exprt(
      result.fraction, have_remainder, unsignedbv_typet(div_width+1));

  // We will subtract the exponents;
  // to account for overflow, we add a bit.
  const typecast_exprt exponent1(
    unpacked1.exponent, signedbv_typet(spec.e + 1));
  const typecast_exprt exponent2(
    unpacked2.exponent, signedbv_typet(spec.e + 1));

  // subtract exponents
  const minus_exprt added_exponent(exponent1, exponent2);

  // adjust, as we have thown in extra fraction bits
  result.exponent=plus_exprt(
    added_exponent,
    from_integer(spec.f, added_exponent.type()));

  // new sign
  result.sign=notequal_exprt(unpacked1.sign, unpacked2.sign);

  // Infinity? This happens when
  // 1) dividing a non-nan/non-zero by zero, or
  // 2) first operand is inf and second is non-nan and non-zero
  // In particular, inf/0=inf.
  result.infinity=
    or_exprt(
      and_exprt(not_exprt(unpacked1.zero),
      and_exprt(not_exprt(unpacked1.NaN),
                unpacked2.zero)),
      and_exprt(unpacked1.infinity,
      and_exprt(not_exprt(unpacked2.NaN),
                not_exprt(unpacked2.zero))));

  // NaN?
  result.NaN=or_exprt(unpacked1.NaN,
             or_exprt(unpacked2.NaN,
             or_exprt(and_exprt(unpacked1.zero, unpacked2.zero),
                      and_exprt(unpacked1.infinity, unpacked2.infinity))));

  // Division by infinity produces zero, unless we have NaN
  const and_exprt force_zero(not_exprt(unpacked1.NaN), unpacked2.infinity);

  result.fraction=
    if_exprt(
      force_zero,
      from_integer(0, result.fraction.type()),
      result.fraction);

  return rounder(result, rm, spec);
}

exprt float_bvt::fma(
  const exprt &multiply_lhs,
  const exprt &multiply_rhs,
  const exprt &addend,
  const exprt &rm,
  const ieee_float_spect &spec) const
{
  // Fused multiply-add: round(multiply_lhs * multiply_rhs + addend) with single
  // rounding.  Multiply at double width (exact), add at double width (exact),
  // then round once.

  const unbiased_floatt unpacked_lhs = unpack(multiply_lhs, spec);
  const unbiased_floatt unpacked_rhs = unpack(multiply_rhs, spec);
  const unbiased_floatt unpacked_add = unpack(addend, spec);

  const std::size_t frac_size = spec.f + 1;
  const std::size_t prod_width = frac_size * 2;
  const typet prod_frac_type = unsignedbv_typet(prod_width);

  // Exact product: multiply fractions at double width
  const exprt fraction1 =
    zero_extend_exprt{unpacked_lhs.fraction, prod_frac_type};
  const exprt fraction2 =
    zero_extend_exprt{unpacked_rhs.fraction, prod_frac_type};
  exprt prod_fraction = mult_exprt(fraction1, fraction2);

  const typet wide_exp_type = signedbv_typet(spec.e + 2);
  exprt prod_exponent = plus_exprt(
    typecast_exprt(unpacked_lhs.exponent, wide_exp_type),
    typecast_exprt(unpacked_rhs.exponent, wide_exp_type));
  prod_exponent = plus_exprt(prod_exponent, from_integer(1, wide_exp_type));

  exprt prod_sign = notequal_exprt(unpacked_lhs.sign, unpacked_rhs.sign);

  // Align addend fraction to product width (pad on the right)
  const std::size_t c_pad = prod_width - frac_size;
  exprt c_fraction = concatenation_exprt(
    unpacked_add.fraction,
    from_integer(0, unsignedbv_typet(c_pad)),
    prod_frac_type);
  exprt c_exponent = typecast_exprt(unpacked_add.exponent, wide_exp_type);

  // Add product + c: align fractions by exponent difference
  exprt exp_diff = minus_exprt(prod_exponent, c_exponent);
  exprt c_bigger = sign_exprt(exp_diff);

  exprt bigger_exp = if_exprt(c_bigger, c_exponent, prod_exponent);
  exprt big_frac = if_exprt(c_bigger, c_fraction, prod_fraction);
  exprt small_frac = if_exprt(c_bigger, prod_fraction, c_fraction);

  exprt distance =
    typecast_exprt(abs_exprt(exp_diff), unsignedbv_typet(spec.e + 2));
  exprt limited_dist = limit_distance(distance, prod_width + 3);

  // Pad with 3 guard bits
  const typet padded_type = unsignedbv_typet(prod_width + 3);
  exprt big_padded = concatenation_exprt(
    big_frac, from_integer(0, unsignedbv_typet(3)), padded_type);
  exprt small_padded = concatenation_exprt(
    small_frac, from_integer(0, unsignedbv_typet(3)), padded_type);

  // Shift smaller fraction right, tracking sticky bit
  exprt sticky_bit;
  exprt small_shifted =
    sticky_right_shift(small_padded, limited_dist, sticky_bit);
  small_shifted =
    bitor_exprt(small_shifted, typecast_exprt(sticky_bit, padded_type));

  // Extend for potential carry/borrow
  const typet sum_type = unsignedbv_typet(prod_width + 5);
  exprt big_ext = zero_extend_exprt{big_padded, sum_type};
  exprt small_ext = zero_extend_exprt{small_shifted, sum_type};

  // Add or subtract based on signs
  exprt subtract_lit = notequal_exprt(prod_sign, unpacked_add.sign);
  exprt sum = if_exprt(
    subtract_lit,
    minus_exprt(big_ext, small_ext),
    plus_exprt(big_ext, small_ext));

  // Handle negative result (from subtraction)
  exprt fraction_sign =
    sign_exprt(typecast_exprt(sum, signedbv_typet(prod_width + 5)));
  sum = if_exprt(
    fraction_sign,
    unary_minus_exprt(typecast_exprt(sum, signedbv_typet(prod_width + 5))),
    typecast_exprt(sum, signedbv_typet(prod_width + 5)));
  sum = typecast_exprt(sum, sum_type);

  unbiased_floatt result;
  result.fraction = sum;
  result.exponent = plus_exprt(
    typecast_exprt(bigger_exp, signedbv_typet(spec.e + 3)),
    from_integer(2, signedbv_typet(spec.e + 3)));

  // Sign
  exprt add_sub_sign = notequal_exprt(
    if_exprt(c_bigger, unpacked_add.sign, prod_sign), fraction_sign);
  result.sign = add_sub_sign;

  // NaN
  exprt prod_inf = or_exprt(unpacked_lhs.infinity, unpacked_rhs.infinity);
  result.NaN = disjunction(
    {isnan(multiply_lhs, spec),
     isnan(multiply_rhs, spec),
     isnan(addend, spec),
     and_exprt(unpacked_lhs.zero, unpacked_rhs.infinity),
     and_exprt(unpacked_rhs.zero, unpacked_lhs.infinity),
     and_exprt(
       and_exprt(prod_inf, unpacked_add.infinity),
       notequal_exprt(prod_sign, unpacked_add.sign))});

  // Infinity
  result.infinity =
    and_exprt(not_exprt(result.NaN), or_exprt(prod_inf, unpacked_add.infinity));

  return rounder(result, rm, spec);
}

exprt float_bvt::relation(
  const exprt &src1,
  relt rel,
  const exprt &src2,
  const ieee_float_spect &spec)
{
  if(rel==relt::GT)
    return relation(src2, relt::LT, src1, spec); // swapped
  else if(rel==relt::GE)
    return relation(src2, relt::LE, src1, spec); // swapped

  INVARIANT(
    rel == relt::EQ || rel == relt::LT || rel == relt::LE,
    "relation should be equality, less-than, or less-or-equal");

  // special cases: -0 and 0 are equal
  const exprt is_zero1 = is_zero(src1);
  const exprt is_zero2 = is_zero(src2);
  const and_exprt both_zero(is_zero1, is_zero2);

  // NaN compares to nothing
  exprt isnan1=isnan(src1, spec);
  exprt isnan2=isnan(src2, spec);
  const or_exprt nan(isnan1, isnan2);

  if(rel==relt::LT || rel==relt::LE)
  {
    const equal_exprt bitwise_equal(src1, src2);

    // signs different? trivial! Unless Zero.

    const notequal_exprt signs_different(sign_bit(src1), sign_bit(src2));

    // as long as the signs match: compare like unsigned numbers

    // this works due to the BIAS
    const binary_relation_exprt less_than1(
      typecast_exprt(
        typecast_exprt(src1, bv_typet(spec.width())),
        unsignedbv_typet(spec.width())),
      ID_lt,
      typecast_exprt(
        typecast_exprt(src2, bv_typet(spec.width())),
        unsignedbv_typet(spec.width())));

    // if both are negative (and not the same), need to turn around!
    const notequal_exprt less_than2(
      less_than1, and_exprt(sign_bit(src1), sign_bit(src2)));

    const if_exprt less_than3(signs_different, sign_bit(src1), less_than2);

    if(rel==relt::LT)
    {
      and_exprt and_bv{{less_than3,
                        // for the case of two negative numbers
                        not_exprt(bitwise_equal),
                        not_exprt(both_zero),
                        not_exprt(nan)}};

      return std::move(and_bv);
    }
    else if(rel==relt::LE)
    {
      or_exprt or_bv{{less_than3, both_zero, bitwise_equal}};

      return and_exprt(or_bv, not_exprt(nan));
    }
    else
      UNREACHABLE;
  }
  else if(rel==relt::EQ)
  {
    const equal_exprt bitwise_equal(src1, src2);

    return and_exprt(
      or_exprt(bitwise_equal, both_zero),
      not_exprt(nan));
  }

  UNREACHABLE;
  return false_exprt();
}

exprt float_bvt::isinf(
  const exprt &src,
  const ieee_float_spect &spec)
{
  return and_exprt(
    exponent_all_ones(src, spec),
    fraction_all_zeros(src, spec));
}

exprt float_bvt::isfinite(
  const exprt &src,
  const ieee_float_spect &spec)
{
  return not_exprt(or_exprt(isinf(src, spec), isnan(src, spec)));
}

/// Gets the unbiased exponent in a floating-point bit-vector
exprt float_bvt::get_exponent(
  const exprt &src,
  const ieee_float_spect &spec)
{
  return extractbits_exprt(src, spec.f, unsignedbv_typet(spec.e));
}

/// Gets the fraction without hidden bit in a floating-point bit-vector src
exprt float_bvt::get_fraction(
  const exprt &src,
  const ieee_float_spect &spec)
{
  return extractbits_exprt(src, 0, unsignedbv_typet(spec.f));
}

exprt float_bvt::isnan(
  const exprt &src,
  const ieee_float_spect &spec)
{
  return and_exprt(exponent_all_ones(src, spec),
                   not_exprt(fraction_all_zeros(src, spec)));
}

/// normalize fraction/exponent pair returns 'zero' if fraction is zero
void float_bvt::normalization_shift(
  exprt &fraction,
  exprt &exponent)
{
  // n-log-n alignment shifter.
  // The worst-case shift is the number of fraction
  // bits minus one, in case the fraction is one exactly.
  std::size_t fraction_bits=to_unsignedbv_type(fraction.type()).get_width();
  std::size_t exponent_bits=to_signedbv_type(exponent.type()).get_width();
  PRECONDITION(fraction_bits != 0);

  std::size_t depth = address_bits(fraction_bits - 1);

  exponent = typecast_exprt(
    exponent, signedbv_typet(std::max(depth, exponent_bits + 1)));

  exprt exponent_delta=from_integer(0, exponent.type());

  for(int d=depth-1; d>=0; d--)
  {
    unsigned distance=(1<<d);
    INVARIANT(
      fraction_bits > distance,
      "distance must be within the range of fraction bits");

    // check if first 'distance'-many bits are zeros
    const extractbits_exprt prefix(
      fraction, fraction_bits - distance, unsignedbv_typet(distance));
    const equal_exprt prefix_is_zero(prefix, from_integer(0, prefix.type()));

    // If so, shift the zeros out left by 'distance'.
    // Otherwise, leave as is.
    const shl_exprt shifted(fraction, distance);

    fraction=
      if_exprt(prefix_is_zero, shifted, fraction);

    // add corresponding weight to exponent
    INVARIANT(
      d < (signed int)exponent_bits,
      "depth must be smaller than exponent bits");

    exponent_delta=
      bitor_exprt(exponent_delta,
        shl_exprt(typecast_exprt(prefix_is_zero, exponent_delta.type()), d));
  }

  exponent=minus_exprt(exponent, exponent_delta);
}

/// make sure exponent is not too small; the exponent is unbiased
void float_bvt::denormalization_shift(
  exprt &fraction,
  exprt &exponent,
  const ieee_float_spect &spec)
{
  mp_integer bias=spec.bias();

  // Is the exponent strictly less than -bias+1, i.e., exponent<-bias+1?
  // This is transformed to distance=(-bias+1)-exponent
  // i.e., distance>0
  // Note that 1-bias is the exponent represented by 0...01,
  // i.e. the exponent of the smallest normal number and thus the 'base'
  // exponent for subnormal numbers.

  std::size_t exponent_bits=to_signedbv_type(exponent.type()).get_width();
  PRECONDITION(exponent_bits >= spec.e);

#if 1
  // Need to sign extend to avoid overflow.  Note that this is a
  // relatively rare problem as the value needs to be close to the top
  // of the exponent range and then range must not have been
  // previously extended as add, multiply, etc. do.  This is primarily
  // to handle casting down from larger ranges.
  exponent=typecast_exprt(exponent, signedbv_typet(exponent_bits+1));
#endif

  const minus_exprt distance(
    from_integer(-bias + 1, exponent.type()), exponent);

  // use sign bit
  const and_exprt denormal(
    not_exprt(sign_exprt(distance)),
    notequal_exprt(distance, from_integer(0, distance.type())));

#if 1
  // Care must be taken to not loose information required for the
  // guard and sticky bits.  +3 is for the hidden, guard and sticky bits.
  std::size_t fraction_bits=to_unsignedbv_type(fraction.type()).get_width();

  if(fraction_bits < spec.f+3)
  {
    // Add zeros at the LSB end for the guard bit to shift into
    fraction=
      concatenation_exprt(
        fraction, unsignedbv_typet(spec.f + 3 - fraction_bits).zero_expr(),
        unsignedbv_typet(spec.f+3));
  }

  exprt denormalisedFraction = fraction;

  exprt sticky_bit = false_exprt();
  denormalisedFraction =
    sticky_right_shift(fraction, distance, sticky_bit);

  denormalisedFraction=
    bitor_exprt(denormalisedFraction,
      typecast_exprt(sticky_bit, denormalisedFraction.type()));

  fraction=
    if_exprt(
      denormal,
      denormalisedFraction,
      fraction);

#else
  fraction=
    if_exprt(
      denormal,
      lshr_exprt(fraction, distance),
      fraction);
#endif

  exponent=
    if_exprt(denormal,
      from_integer(-bias, exponent.type()),
      exponent);
}

exprt float_bvt::rounder(
  const unbiased_floatt &src,
  const exprt &rm,
  const ieee_float_spect &spec) const
{
  // incoming: some fraction (with explicit 1),
  //           some exponent without bias
  // outgoing: rounded, with right size, with hidden bit, bias

  exprt aligned_fraction=src.fraction,
        aligned_exponent=src.exponent;

  {
    std::size_t exponent_bits = std::max(address_bits(spec.f), spec.e) + 1;

    // before normalization, make sure exponent is large enough
    if(to_signedbv_type(aligned_exponent.type()).get_width()<exponent_bits)
    {
      // sign extend
      aligned_exponent=
        typecast_exprt(aligned_exponent, signedbv_typet(exponent_bits));
    }
  }

  // align it!
  normalization_shift(aligned_fraction, aligned_exponent);
  denormalization_shift(aligned_fraction, aligned_exponent, spec);

  unbiased_floatt result;
  result.fraction=aligned_fraction;
  result.exponent=aligned_exponent;
  result.sign=src.sign;
  result.NaN=src.NaN;
  result.infinity=src.infinity;

  rounding_mode_bitst rounding_mode_bits(rm);
  round_fraction(result, rounding_mode_bits, spec);
  round_exponent(result, rounding_mode_bits, spec);

  return pack(bias(result, spec), spec);
}

/// rounding decision for fraction using sticky bit
exprt float_bvt::fraction_rounding_decision(
  const std::size_t dest_bits,
  const exprt sign,
  const exprt &fraction,
  const rounding_mode_bitst &rounding_mode_bits)
{
  std::size_t fraction_bits=
    to_unsignedbv_type(fraction.type()).get_width();

  PRECONDITION(dest_bits < fraction_bits);

  // we have too many fraction bits
  std::size_t extra_bits=fraction_bits-dest_bits;

  // more than two extra bits are superflus, and are
  // turned into a sticky bit

  exprt sticky_bit=false_exprt();

  if(extra_bits>=2)
  {
    // We keep most-significant bits, and thus the tail is made
    // of least-significant bits.
    const extractbits_exprt tail(
      fraction, 0, unsignedbv_typet(extra_bits - 2 + 1));
    sticky_bit=notequal_exprt(tail, from_integer(0, tail.type()));
  }

  // the rounding bit is the last extra bit
  INVARIANT(
    extra_bits >= 1, "the extra bits contain at least the rounding bit");
  const extractbit_exprt rounding_bit(fraction, extra_bits - 1);

  // we get one bit of the fraction for some rounding decisions
  const extractbit_exprt rounding_least(fraction, extra_bits);

  // round-to-nearest (ties to even)
  const and_exprt round_to_even(
    rounding_bit, or_exprt(rounding_least, sticky_bit));

  // round up
  const and_exprt round_to_plus_inf(
    not_exprt(sign), or_exprt(rounding_bit, sticky_bit));

  // round down
  const and_exprt round_to_minus_inf(sign, or_exprt(rounding_bit, sticky_bit));

  // round to zero
  false_exprt round_to_zero;

  // round-to-nearest (ties to away)
  const auto round_to_away = rounding_bit;

  // now select appropriate one
  // clang-format off
  return if_exprt(rounding_mode_bits.round_to_even, round_to_even,
         if_exprt(rounding_mode_bits.round_to_plus_inf, round_to_plus_inf,
         if_exprt(rounding_mode_bits.round_to_minus_inf, round_to_minus_inf,
         if_exprt(rounding_mode_bits.round_to_zero, round_to_zero,
         if_exprt(rounding_mode_bits.round_to_away, round_to_away,
           false_exprt()))))); // otherwise zero
  // clang-format off
}

void float_bvt::round_fraction(
  unbiased_floatt &result,
  const rounding_mode_bitst &rounding_mode_bits,
  const ieee_float_spect &spec)
{
  std::size_t fraction_size=spec.f+1;
  std::size_t result_fraction_size=
    to_unsignedbv_type(result.fraction.type()).get_width();

  // do we need to enlarge the fraction?
  if(result_fraction_size<fraction_size)
  {
    // pad with zeros at bottom
    std::size_t padding=fraction_size-result_fraction_size;

    result.fraction=concatenation_exprt(
      result.fraction,
      unsignedbv_typet(padding).zero_expr(),
      unsignedbv_typet(fraction_size));
  }
  else if(result_fraction_size==fraction_size) // it stays
  {
    // do nothing
  }
  else // fraction gets smaller -- rounding
  {
    std::size_t extra_bits=result_fraction_size-fraction_size;
    INVARIANT(
      extra_bits >= 1, "the extra bits include at least the rounding bit");

    // this computes the rounding decision
    exprt increment=fraction_rounding_decision(
      fraction_size, result.sign, result.fraction, rounding_mode_bits);

    // chop off all the extra bits
    result.fraction = extractbits_exprt(
      result.fraction, extra_bits, unsignedbv_typet(fraction_size));

#if 0
    // *** does not catch when the overflow goes subnormal -> normal ***
    // incrementing the fraction might result in an overflow
    result.fraction=
      bv_utils.zero_extension(result.fraction, result.fraction.size()+1);

    result.fraction=bv_utils.incrementer(result.fraction, increment);

    exprt overflow=result.fraction.back();

    // In case of an overflow, the exponent has to be incremented.
    // "Post normalization" is then required.
    result.exponent=
      bv_utils.incrementer(result.exponent, overflow);

    // post normalization of the fraction
    exprt integer_part1=result.fraction.back();
    exprt integer_part0=result.fraction[result.fraction.size()-2];
    const or_exprt new_integer_part(integer_part1, integer_part0);

    result.fraction.resize(result.fraction.size()-1);
    result.fraction.back()=new_integer_part;

#else
    // When incrementing due to rounding there are two edge
    // cases we need to be aware of:
    //  1. If the number is normal, the increment can overflow.
    //     In this case we need to increment the exponent and
    //     set the MSB of the fraction to 1.
    //  2. If the number is the largest subnormal, the increment
    //     can change the MSB making it normal.  Thus the exponent
    //     must be incremented but the fraction will be OK.
    const extractbit_exprt old_msb(result.fraction, fraction_size - 1);

    // increment if 'increment' is true
    result.fraction=
      plus_exprt(result.fraction,
                 typecast_exprt(increment, result.fraction.type()));

    // Normal overflow when old MSB == 1 and new MSB == 0
    const extractbit_exprt new_msb(result.fraction, fraction_size - 1);
    const and_exprt overflow(old_msb, not_exprt(new_msb));

    // Subnormal to normal transition when old MSB == 0 and new MSB == 1
    const and_exprt subnormal_to_normal(not_exprt(old_msb), new_msb);

    // In case of an overflow or subnormal to normal conversion,
    // the exponent has to be incremented.
    result.exponent=
      plus_exprt(
        result.exponent,
        if_exprt(
          or_exprt(overflow, subnormal_to_normal),
          from_integer(1, result.exponent.type()),
          from_integer(0, result.exponent.type())));

    // post normalization of the fraction
    // In the case of overflow, set the MSB to 1
    // The subnormal case will have (only) the MSB set to 1
    result.fraction=bitor_exprt(
      result.fraction,
      if_exprt(overflow,
               from_integer(1<<(fraction_size-1), result.fraction.type()),
               from_integer(0, result.fraction.type())));
#endif
  }
}

void float_bvt::round_exponent(
  unbiased_floatt &result,
  const rounding_mode_bitst &rounding_mode_bits,
  const ieee_float_spect &spec)
{
  std::size_t result_exponent_size=
    to_signedbv_type(result.exponent.type()).get_width();

  PRECONDITION(result_exponent_size >= spec.e);

  // do we need to enlarge the exponent?
  if(result_exponent_size == spec.e) // it stays
  {
    // do nothing
  }
  else // exponent gets smaller -- chop off top bits
  {
    exprt old_exponent=result.exponent;
    result.exponent =
      extractbits_exprt(result.exponent, 0, signedbv_typet(spec.e));

    // max_exponent is the maximum representable
    // i.e. 1 higher than the maximum possible for a normal number
    exprt max_exponent=
      from_integer(
        spec.max_exponent()-spec.bias(), old_exponent.type());

    // the exponent is garbage if the fractional is zero

    const and_exprt exponent_too_large(
      binary_relation_exprt(old_exponent, ID_ge, max_exponent),
      notequal_exprt(result.fraction, from_integer(0, result.fraction.type())));

#if 1
    // Directed rounding modes round overflow to the maximum normal
    // depending on the particular mode and the sign
    const or_exprt overflow_to_inf(
      rounding_mode_bits.round_to_even,
      or_exprt(
        and_exprt(rounding_mode_bits.round_to_plus_inf, not_exprt(result.sign)),
        and_exprt(rounding_mode_bits.round_to_minus_inf, result.sign)));

    const and_exprt set_to_max(exponent_too_large, not_exprt(overflow_to_inf));

    exprt largest_normal_exponent=
      from_integer(
        spec.max_exponent()-(spec.bias() + 1), result.exponent.type());

    result.exponent=
      if_exprt(set_to_max, largest_normal_exponent, result.exponent);

    result.fraction=
      if_exprt(set_to_max,
               to_unsignedbv_type(result.fraction.type()).largest_expr(),
               result.fraction);

    result.infinity=or_exprt(result.infinity,
                             and_exprt(exponent_too_large,
                                       overflow_to_inf));
#else
    result.infinity=or_exprt(result.infinity, exponent_too_large);
#endif
  }
}

/// takes an unbiased float, and applies the bias
float_bvt::biased_floatt float_bvt::bias(
  const unbiased_floatt &src,
  const ieee_float_spect &spec)
{
  biased_floatt result;

  result.sign=src.sign;
  result.NaN=src.NaN;
  result.infinity=src.infinity;

  // we need to bias the new exponent
  result.exponent=add_bias(src.exponent, spec);

  // strip off the hidden bit
  PRECONDITION(
    to_unsignedbv_type(src.fraction.type()).get_width() == spec.f + 1);

  const extractbit_exprt hidden_bit(src.fraction, spec.f);
  const not_exprt denormal(hidden_bit);

  result.fraction =
    extractbits_exprt(src.fraction, 0, unsignedbv_typet(spec.f));

  // make exponent zero if its denormal
  // (includes zero)
  result.exponent=
    if_exprt(denormal, from_integer(0, result.exponent.type()),
             result.exponent);

  return result;
}

exprt float_bvt::add_bias(
  const exprt &src,
  const ieee_float_spect &spec)
{
  typet t=unsignedbv_typet(spec.e);
  return plus_exprt(
    typecast_exprt(src, t),
    from_integer(spec.bias(), t));
}

exprt float_bvt::sub_bias(
  const exprt &src,
  const ieee_float_spect &spec)
{
  typet t=signedbv_typet(spec.e);
  return minus_exprt(
    typecast_exprt(src, t),
    from_integer(spec.bias(), t));
}

float_bvt::unbiased_floatt float_bvt::unpack(
  const exprt &src,
  const ieee_float_spect &spec)
{
  unbiased_floatt result;

  result.sign=sign_bit(src);

  result.fraction=get_fraction(src, spec);

  // add hidden bit
  exprt hidden_bit=isnormal(src, spec);
  result.fraction=
    concatenation_exprt(hidden_bit, result.fraction,
      unsignedbv_typet(spec.f+1));

  result.exponent=get_exponent(src, spec);

  // unbias the exponent
  exprt denormal=exponent_all_zeros(src, spec);

  result.exponent=
    if_exprt(denormal,
      from_integer(-spec.bias()+1, signedbv_typet(spec.e)),
      sub_bias(result.exponent, spec));

  result.infinity=isinf(src, spec);
  result.zero = is_zero(src);
  result.NaN=isnan(src, spec);

  return result;
}

exprt float_bvt::pack(
  const biased_floatt &src,
  const ieee_float_spect &spec)
{
  PRECONDITION(to_unsignedbv_type(src.fraction.type()).get_width() == spec.f);
  PRECONDITION(to_unsignedbv_type(src.exponent.type()).get_width() == spec.e);

  // do sign -- we make this 'false' for NaN
  const if_exprt sign_bit(src.NaN, false_exprt(), src.sign);

  // the fraction is zero in case of infinity,
  // and one in case of NaN
  const if_exprt fraction(
    src.NaN,
    from_integer(1, src.fraction.type()),
    if_exprt(src.infinity, from_integer(0, src.fraction.type()), src.fraction));

  const or_exprt infinity_or_NaN(src.NaN, src.infinity);

  // do exponent
  const if_exprt exponent(
    infinity_or_NaN, from_integer(-1, src.exponent.type()), src.exponent);

  // stitch all three together
  return typecast_exprt(
    concatenation_exprt(
      {std::move(sign_bit), std::move(exponent), std::move(fraction)},
      bv_typet(spec.f + spec.e + 1)),
    spec.to_type());
}

exprt float_bvt::sticky_right_shift(
  const exprt &op,
  const exprt &dist,
  exprt &sticky)
{
  std::size_t d=1, width=to_unsignedbv_type(op.type()).get_width();
  exprt result=op;
  sticky=false_exprt();

  std::size_t dist_width=to_bitvector_type(dist.type()).get_width();

  for(std::size_t stage=0; stage<dist_width; stage++)
  {
    const lshr_exprt tmp(result, d);

    exprt lost_bits;

    if(d<=width)
      lost_bits = extractbits_exprt(result, 0, unsignedbv_typet(d));
    else
      lost_bits=result;

    const extractbit_exprt dist_bit(dist, stage);

    sticky=
      or_exprt(
        and_exprt(
          dist_bit,
          notequal_exprt(lost_bits, from_integer(0, lost_bits.type()))),
        sticky);

    result=if_exprt(dist_bit, tmp, result);

    d=d<<1;
  }

  return result;
}
