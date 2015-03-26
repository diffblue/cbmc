/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/expr_util.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>

#include "float_bv.h"

/*******************************************************************\

Function: float_bvt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::convert(const exprt &expr)
{
  if(expr.id()==ID_abs)
    return abs(to_abs_expr(expr).op(), get_spec(expr));
  else if(expr.id()==ID_unary_minus)
    return negation(to_unary_minus_expr(expr).op(), get_spec(expr));
  else if(expr.id()==ID_ieee_float_equal)
    return is_equal(expr.op0(), expr.op1(), get_spec(expr.op0()));
  else if(expr.id()==ID_ieee_float_notequal)
    return not_exprt(is_equal(expr.op0(), expr.op1(), get_spec(expr.op0())));
  else if(expr.id()==ID_floatbv_typecast)
  {
    const typet &src_type=expr.op0().type();
    const typet &dest_type=expr.type();
    
    if(dest_type.id()==ID_signedbv &&
       src_type.id()==ID_floatbv) // float -> signed
      return to_signed_integer(
        expr.op0(), to_signedbv_type(dest_type).get_width(), expr.op1(), get_spec(expr.op0()));
    else if(dest_type.id()==ID_unsignedbv &&
            src_type.id()==ID_floatbv) // float -> unsigned
      return to_unsigned_integer(
        expr.op0(), to_unsignedbv_type(dest_type).get_width(), expr.op1(), get_spec(expr.op0()));
    else if(src_type.id()==ID_signedbv &&
            dest_type.id()==ID_floatbv) // signed -> float
      return from_signed_integer(
        expr.op0(), expr.op1(), get_spec(expr));
    else if(src_type.id()==ID_unsignedbv &&
            dest_type.id()==ID_floatbv) // unsigned -> float
      return from_unsigned_integer(
        expr.op0(), expr.op1(), get_spec(expr));
    else if(dest_type.id()==ID_floatbv &&
            src_type.id()==ID_floatbv) // float -> float
      return conversion(expr.op0(), expr.op1(), get_spec(expr.op0()), get_spec(expr));
    else
      return nil_exprt();
  }
  else if(expr.id()==ID_typecast &&
	  expr.type().id()==ID_bool &&
	  expr.op0().type().id()==ID_floatbv)  // float -> bool
    return not_exprt(is_zero(expr.op0(), get_spec(expr.op0())));
  else if(expr.id()==ID_floatbv_plus)
    return add_sub(false, expr.op0(), expr.op1(), expr.op2(), get_spec(expr));
  else if(expr.id()==ID_floatbv_minus)
    return add_sub(true, expr.op0(), expr.op1(), expr.op2(), get_spec(expr));
  else if(expr.id()==ID_floatbv_mult)
    return mul(expr.op0(), expr.op1(), expr.op2(), get_spec(expr));
  else if(expr.id()==ID_floatbv_div)
    return div(expr.op0(), expr.op1(), expr.op2(), get_spec(expr));
  else if(expr.id()==ID_isnan)
    return isnan(expr.op0(), get_spec(expr.op0()));
  else if(expr.id()==ID_isfinite)
    return isfinite(expr.op0(), get_spec(expr.op0()));
  else if(expr.id()==ID_isinf)
    return isinf(expr.op0(), get_spec(expr.op0()));
  else if(expr.id()==ID_isnormal)
    return isnormal(expr.op0(), get_spec(expr.op0()));
  else if(expr.id()==ID_lt)
    return relation(expr.op0(), LT, expr.op1(), get_spec(expr.op0()));
  else if(expr.id()==ID_gt)
    return relation(expr.op0(), GT, expr.op1(), get_spec(expr.op0()));
  else if(expr.id()==ID_le)
    return relation(expr.op0(), LE, expr.op1(), get_spec(expr.op0()));
  else if(expr.id()==ID_ge)
    return relation(expr.op0(), GE, expr.op1(), get_spec(expr.op0()));
  else if(expr.id()==ID_sign)
    return sign_bit(expr.op0());

  return nil_exprt();
}

/*******************************************************************\

Function: float_bvt::get_spec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ieee_float_spect float_bvt::get_spec(const exprt &expr)
{
  const floatbv_typet &type=to_floatbv_type(expr.type());
  return ieee_float_spect(type);
}

/*******************************************************************\

Function: float_bvt::abs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::abs(const exprt &op, const ieee_float_spect &spec)
{
  // we mask away the sign bit, which is the most significand bit
  std::string mask_str;
  mask_str.resize(spec.width(), '1');
  mask_str[0]='0';
  
  constant_exprt mask(mask_str, op.type());
  
  return bitand_exprt(op, mask);
}

/*******************************************************************\

Function: float_bvt::negation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::negation(const exprt &op, const ieee_float_spect &spec)
{
  // we flip the sign bit with an xor
  std::string mask_str;
  mask_str.resize(spec.width(), '0');
  mask_str[0]='1';
  
  constant_exprt mask(mask_str, op.type());
  
  return bitxor_exprt(op, mask);
}

/*******************************************************************\

Function: float_bvt::is_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::is_equal(
  const exprt &src0,
  const exprt &src1,
  const ieee_float_spect &spec)
{
  // special cases: -0 and 0 are equal
  exprt is_zero0=is_zero(src0, spec);
  exprt is_zero1=is_zero(src1, spec);
  exprt both_zero=and_exprt(is_zero0, is_zero1);

  // NaN compares to nothing
  exprt isnan0=isnan(src0, spec);
  exprt isnan1=isnan(src1, spec);
  exprt nan=or_exprt(isnan0, isnan1);

  exprt bitwise_equal=equal_exprt(src0, src1);

  return and_exprt(
    or_exprt(bitwise_equal, both_zero),
    not_exprt(nan));
}

/*******************************************************************\

Function: float_bvt::is_zero

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::is_zero(
  const exprt &src,
  const ieee_float_spect &spec)
{
  // we mask away the sign bit, which is the most significand bit
  const floatbv_typet &type=to_floatbv_type(src.type());
  unsigned width=type.get_width();
  
  std::string mask_str;
  mask_str.resize(width, '1');
  mask_str[0]='0';
  
  constant_exprt mask(mask_str, src.type());
  
  return equal_exprt(
    bitand_exprt(src, mask),
    gen_zero(src.type()));
}

/*******************************************************************\

Function: float_bvt::exponent_all_ones

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::exponent_all_ones(
  const exprt &src,
  const ieee_float_spect &spec)
{
  exprt exponent=get_exponent(src, spec);
  exprt all_ones=to_unsignedbv_type(exponent.type()).largest_expr();
  return equal_exprt(exponent, all_ones);
}

/*******************************************************************\

Function: float_bvt::exponent_all_zeros

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::exponent_all_zeros(
  const exprt &src,
  const ieee_float_spect &spec)
{
  exprt exponent=get_exponent(src, spec);
  exprt all_zeros=to_unsignedbv_type(exponent.type()).zero_expr();
  return equal_exprt(exponent, all_zeros);
}

/*******************************************************************\

Function: float_bvt::fraction_all_zeros

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::fraction_all_zeros(
  const exprt &src,
  const ieee_float_spect &spec)
{
  // does not include hidden bit
  exprt fraction=get_fraction(src, spec);
  exprt all_zeros=to_unsignedbv_type(fraction.type()).zero_expr();
  return equal_exprt(fraction, all_zeros);
}

/*******************************************************************\

Function: float_bvt::rounding_mode_bitst::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void float_bvt::rounding_mode_bitst::get(const exprt &rm)
{
  exprt round_to_even_const=from_integer(ieee_floatt::ROUND_TO_EVEN, rm.type());
  exprt round_to_plus_inf_const=from_integer(ieee_floatt::ROUND_TO_PLUS_INF, rm.type());
  exprt round_to_minus_inf_const=from_integer(ieee_floatt::ROUND_TO_MINUS_INF, rm.type());
  exprt round_to_zero_const=from_integer(ieee_floatt::ROUND_TO_ZERO, rm.type());

  round_to_even=equal_exprt(rm, round_to_even_const);
  round_to_plus_inf=equal_exprt(rm, round_to_plus_inf_const);
  round_to_minus_inf=equal_exprt(rm, round_to_minus_inf_const);
  round_to_zero=equal_exprt(rm, round_to_zero_const);
}

/*******************************************************************\

Function: float_bvt::sign_bit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::sign_bit(const exprt &op)
{
  const bitvector_typet &bv_type=to_bitvector_type(op.type());
  unsigned width=bv_type.get_width();
  return extractbit_exprt(op, width-1);
}

/*******************************************************************\

Function: float_bvt::from_signed_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::from_signed_integer(
  const exprt &src,
  const exprt &rm,
  const ieee_float_spect &spec)
{
  unsigned src_width=to_signedbv_type(src.type()).get_width();

  unbiased_floatt result;

  // we need to adjust for negative integers
  result.sign=sign_bit(src);

  result.fraction=
    typecast_exprt(abs_exprt(src), unsignedbv_typet(src_width));
  
  // build an exponent (unbiased) -- this is signed!
  result.exponent=
    from_integer(
      src_width-1,
      signedbv_typet(address_bits(src_width-1).to_long()+1));

  return rounder(result, rm, spec);
}

/*******************************************************************\

Function: float_bvt::from_unsigned_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::from_unsigned_integer(
  const exprt &src,
  const exprt &rm,
  const ieee_float_spect &spec)
{
  unbiased_floatt result;

  result.fraction=src;

  unsigned src_width=to_unsignedbv_type(src.type()).get_width();

  // build an exponent (unbiased) -- this is signed!
  result.exponent=
    from_integer(
      src_width-1,
      signedbv_typet(address_bits(src_width-1).to_long()+1));

  result.sign=false_exprt();

  return rounder(result, rm, spec);
}

/*******************************************************************\

Function: float_bvt::to_signed_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::to_signed_integer(
  const exprt &src,
  unsigned dest_width,
  const exprt &rm,
  const ieee_float_spect &spec)
{
  return to_integer(src, dest_width, true, rm, spec);
}

/*******************************************************************\

Function: float_bvt::to_unsigned_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::to_unsigned_integer(
  const exprt &src,
  unsigned dest_width,
  const exprt &rm,
  const ieee_float_spect &spec)
{
  return to_integer(src, dest_width, false, rm, spec);
}

/*******************************************************************\

Function: float_bvt::to_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::to_integer(
  const exprt &src,
  unsigned dest_width,
  bool is_signed,
  const exprt &rm,
  const ieee_float_spect &spec)
{
  const unbiased_floatt unpacked=unpack(src, spec);
  
  rounding_mode_bitst rounding_mode_bits(rm);

  // Right now hard-wired to round-to-zero, which is
  // the usual case in ANSI-C.

  // if the exponent is positive, shift right
  exprt offset=from_integer(spec.f, signedbv_typet(spec.e));
  exprt distance=minus_exprt(offset, unpacked.exponent);
  exprt shift_result=lshr_exprt(unpacked.fraction, distance);

  // if the exponent is negative, we have zero anyways
  exprt result=shift_result;
  exprt exponent_sign=sign_exprt(unpacked.exponent);

  result=
    if_exprt(exponent_sign, gen_zero(result.type()), result);

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

/*******************************************************************\

Function: float_bvt::conversion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::conversion(
  const exprt &src,
  const exprt &rm,
  const ieee_float_spect &src_spec,
  const ieee_float_spect &dest_spec)
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
    unsigned padding=dest_spec.f-src_spec.f;
    result.fraction=
      concatenation_exprt(
	unpacked_src.fraction,		  
	from_integer(0, unsignedbv_typet(padding)),
        unsignedbv_typet(dest_spec.f+1));
    
    // the exponent gets sign-extended
    assert(unpacked_src.exponent.type().id()==ID_signedbv);
    result.exponent=
      typecast_exprt(unpacked_src.exponent, signedbv_typet(dest_spec.e));

    // if the number was denormal and is normal in the new format,
    // normalise it!
    if(dest_spec.e > src_spec.e)
      normalization_shift(result.fraction, result.exponent);

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

/*******************************************************************\

Function: float_bvt::isnormal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::isnormal(
  const exprt &src,
  const ieee_float_spect &spec)
{
  return and_exprt(
           not_exprt(exponent_all_zeros(src, spec)),
           not_exprt(exponent_all_ones(src, spec)));
}

/*******************************************************************\

Function: float_bvt::subtract_exponents

  Inputs:

 Outputs:

 Purpose: Subtracts the exponents

\*******************************************************************/

exprt float_bvt::subtract_exponents(
  const unbiased_floatt &src1,
  const unbiased_floatt &src2)
{
  // extend both by one bit
  unsigned old_width1=to_signedbv_type(src1.exponent.type()).get_width();
  unsigned old_width2=to_signedbv_type(src2.exponent.type()).get_width();
  assert(old_width1==old_width2);
  
  exprt extended_exponent1=typecast_exprt(src1.exponent, signedbv_typet(old_width1+1));
  exprt extended_exponent2=typecast_exprt(src2.exponent, signedbv_typet(old_width2+1));

  assert(extended_exponent1.type()==extended_exponent2.type());

  // compute shift distance (here is the subtraction)
  return minus_exprt(extended_exponent1, extended_exponent2);
}

/*******************************************************************\

Function: float_bvt::add_sub

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::add_sub(
  bool subtract,
  const exprt &op0,
  const exprt &op1,
  const exprt &rm,
  const ieee_float_spect &spec)
{
  unbiased_floatt unpacked1=unpack(op0, spec);
  unbiased_floatt unpacked2=unpack(op1, spec);

  // subtract?
  if(subtract)
    unpacked2.sign=not_exprt(unpacked2.sign);

  // figure out which operand has the bigger exponent
  const exprt exponent_difference=subtract_exponents(unpacked1, unpacked2);
  exprt src2_bigger=sign_exprt(exponent_difference);

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
  const exprt fraction1_padded=concatenation_exprt(new_fraction1, three_zeros, unsignedbv_typet(spec.f+4));
  const exprt fraction2_padded=concatenation_exprt(new_fraction2, three_zeros, unsignedbv_typet(spec.f+4));

  // shift new_fraction2
  exprt sticky_bit;
  const exprt fraction1_shifted=fraction1_padded;
  const exprt fraction2_shifted=sticky_right_shift(
    fraction2_padded, limited_dist, sticky_bit);

  // sticky bit: 'or' of the bits lost by the right-shift
  exprt fraction2_stickied=
    bitor_exprt(fraction2_shifted,
		concatenation_exprt(
				    from_integer(0, unsignedbv_typet(spec.f+3)),
				    sticky_bit,
				    fraction2_shifted.type()));

  // need to have two extra fraction bits for addition and rounding
  const exprt fraction1_ext=typecast_exprt(fraction1_shifted, unsignedbv_typet(spec.f+4+2));
  const exprt fraction2_ext=typecast_exprt(fraction2_stickied, unsignedbv_typet(spec.f+4+2));

  unbiased_floatt result;

  // now add/sub them
  exprt subtract_lit=
    notequal_exprt(unpacked1.sign, unpacked2.sign);

  result.fraction=
    if_exprt(subtract_lit,
      minus_exprt(fraction1_ext, fraction2_ext),
      plus_exprt(fraction1_ext, fraction2_ext));

  // sign of result
  unsigned width = to_bitvector_type(result.fraction.type()).get_width();
  exprt fraction_sign=sign_exprt(typecast_exprt(result.fraction, signedbv_typet(width)));
  result.fraction=typecast_exprt(abs_exprt(typecast_exprt(result.fraction, signedbv_typet(width))),
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
  result.zero = and_exprt(
      not_exprt(or_exprt(result.infinity, result.NaN)),
      equal_exprt(result.fraction, gen_zero(result.fraction.type())));

  // sign
  exprt add_sub_sign=
    notequal_exprt(if_exprt(src2_bigger, unpacked2.sign, unpacked1.sign),
                   fraction_sign);

  exprt infinity_sign=
    if_exprt(unpacked1.infinity, unpacked1.sign, unpacked2.sign);

  #if 1
  rounding_mode_bitst rounding_mode_bits(rm);
  
  exprt zero_sign=
    if_exprt(rounding_mode_bits.round_to_minus_inf,
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

/*******************************************************************\

Function: float_bvt::limit_distance

  Inputs:

 Outputs:

 Purpose: Limits the shift distance

\*******************************************************************/

exprt float_bvt::limit_distance(
  const exprt &dist,
  mp_integer limit)
{
  unsigned nb_bits=integer2unsigned(address_bits(limit));
  unsigned dist_width=to_unsignedbv_type(dist.type()).get_width();

  if(dist_width<=nb_bits)
    return dist;

  exprt upper_bits=
    extractbits_exprt(dist, dist_width-1, nb_bits,
                      unsignedbv_typet(dist_width-nb_bits));
  exprt upper_bits_zero=equal_exprt(upper_bits, gen_zero(upper_bits.type()));

  exprt lower_bits=
    extractbits_exprt(dist, nb_bits-1, 0,
                      unsignedbv_typet(nb_bits));

  return if_exprt(
    upper_bits_zero,
    lower_bits,
    unsignedbv_typet(nb_bits).largest_expr());
}

/*******************************************************************\

Function: float_bvt::mul

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::mul(
  const exprt &src1,
  const exprt &src2,
  const exprt &rm,
  const ieee_float_spect &spec)
{
  // unpack
  const unbiased_floatt unpacked1=unpack(src1, spec);
  const unbiased_floatt unpacked2=unpack(src2, spec);

  // zero-extend the fractions (unpacked fraction has the hidden bit)
  typet new_fraction_type=unsignedbv_typet((spec.f+1)*2);
  const exprt fraction1=typecast_exprt(unpacked1.fraction, new_fraction_type);
  const exprt fraction2=typecast_exprt(unpacked2.fraction, new_fraction_type);

  // multiply the fractions
  unbiased_floatt result;
  result.fraction=mult_exprt(fraction1, fraction2);

  // extend exponents to account for overflow
  // add two bits, as we do extra arithmetic on it later
  typet new_exponent_type=signedbv_typet(spec.e+2);
  const exprt exponent1=typecast_exprt(unpacked1.exponent, new_exponent_type);
  const exprt exponent2=typecast_exprt(unpacked2.exponent, new_exponent_type);

  exprt added_exponent=plus_exprt(exponent1, exponent2);

  // Adjust exponent; we are thowing in an extra fraction bit,
  // it has been extended above.
  result.exponent=plus_exprt(added_exponent, gen_one(new_exponent_type));

  // new sign
  result.sign=notequal_exprt(unpacked1.sign, unpacked2.sign);

  // infinity?
  result.infinity=or_exprt(unpacked1.infinity, unpacked2.infinity);

  // NaN?
  {
    exprt NaN_cond(ID_or, bool_typet());

    NaN_cond.copy_to_operands(isnan(src1, spec));
    NaN_cond.copy_to_operands(isnan(src2, spec));

    // infinity * 0 is NaN!
    NaN_cond.copy_to_operands(and_exprt(unpacked1.zero, unpacked2.infinity));
    NaN_cond.copy_to_operands(and_exprt(unpacked2.zero, unpacked1.infinity));

    result.NaN=NaN_cond;
  }

  return rounder(result, rm, spec);
}

/*******************************************************************\

Function: float_bvt::div

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::div(
  const exprt &src1,
  const exprt &src2,
  const exprt &rm,
  const ieee_float_spect &spec)
{
  // unpack
  const unbiased_floatt unpacked1=unpack(src1, spec);
  const unbiased_floatt unpacked2=unpack(src2, spec);
  
  unsigned fraction_width=
    to_unsignedbv_type(unpacked1.fraction.type()).get_width();
  unsigned div_width=fraction_width*2+1;

  // pad fraction1 with zeros
  exprt fraction1=
    concatenation_exprt(
      unpacked1.fraction,
      from_integer(0, unsignedbv_typet(div_width-fraction_width)),
      unsignedbv_typet(div_width));

  // zero-extend fraction2 to match faction1
  const exprt fraction2=
    typecast_exprt(unpacked2.fraction, fraction1.type());

  // divide fractions
  unbiased_floatt result;
  exprt rem;

  // the below should be merged somehow
  result.fraction=div_exprt(fraction1, fraction2);
  rem=mod_exprt(fraction1, fraction2);
  
  // is there a remainder?
  exprt have_remainder=notequal_exprt(rem, gen_zero(rem.type()));
  
  // we throw this into the result, as least-significand bit,
  // to get the right rounding decision
  result.fraction=
    concatenation_exprt(result.fraction, have_remainder, unsignedbv_typet(div_width+1));
    
  // We will subtract the exponents;
  // to account for overflow, we add a bit.
  const exprt exponent1=typecast_exprt(unpacked1.exponent, signedbv_typet(spec.e+1));
  const exprt exponent2=typecast_exprt(unpacked2.exponent, signedbv_typet(spec.e+1));

  // subtract exponents
  exprt added_exponent=minus_exprt(exponent1, exponent2);

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
  exprt force_zero=
    and_exprt(not_exprt(unpacked1.NaN), unpacked2.infinity);
  
  result.fraction=if_exprt(force_zero,
    gen_zero(result.fraction.type()), result.fraction);

  return rounder(result, rm, spec);
}

/*******************************************************************\

Function: float_bvt::relation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::relation(
  const exprt &src1,
  relt rel,
  const exprt &src2,
  const ieee_float_spect &spec)
{
  if(rel==GT)
    return relation(src2, LT, src1, spec); // swapped
  else if(rel==GE)
    return relation(src2, LE, src1, spec); // swapped

  assert(rel==EQ || rel==LT || rel==LE);

  // special cases: -0 and 0 are equal
  exprt is_zero1=is_zero(src1, spec);
  exprt is_zero2=is_zero(src2, spec);
  exprt both_zero=and_exprt(is_zero1, is_zero2);

  // NaN compares to nothing
  exprt isnan1=isnan(src1, spec);
  exprt isnan2=isnan(src2, spec);
  exprt nan=or_exprt(isnan1, isnan2);

  if(rel==LT || rel==LE)
  {
    exprt bitwise_equal=equal_exprt(src1, src2);

    // signs different? trivial! Unless Zero.

    exprt signs_different=
      notequal_exprt(sign_bit(src1), sign_bit(src2));

    // as long as the signs match: compare like unsigned numbers

    // this works due to the BIAS
    exprt less_than1=
      binary_relation_exprt(
	typecast_exprt(typecast_exprt(src1, bv_typet(spec.width())),
		                      unsignedbv_typet(spec.width())),
        ID_lt,
        typecast_exprt(typecast_exprt(src2, bv_typet(spec.width())),
		                      unsignedbv_typet(spec.width())));

    // if both are negative (and not the same), need to turn around!
    exprt less_than2=
        notequal_exprt(less_than1,
                       and_exprt(sign_bit(src1), sign_bit(src2)));

    exprt less_than3=
      if_exprt(signs_different,
        sign_bit(src1),
        less_than2);

    if(rel==LT)
    {
      exprt and_bv(ID_and, bool_typet());
      and_bv.copy_to_operands(less_than3);
      and_bv.copy_to_operands(not_exprt(bitwise_equal)); // for the case of two negative numbers
      and_bv.copy_to_operands(not_exprt(both_zero));
      and_bv.copy_to_operands(not_exprt(nan));

      return and_bv;
    }
    else if(rel==LE)
    {
      exprt or_bv(ID_or, bool_typet());
      or_bv.copy_to_operands(less_than3);
      or_bv.copy_to_operands(both_zero);
      or_bv.copy_to_operands(bitwise_equal);

      return and_exprt(or_bv, not_exprt(nan));
    }
    else
      assert(false);
  }
  else if(rel==EQ)
  {
    exprt bitwise_equal=equal_exprt(src1, src2);

    return and_exprt(
      or_exprt(bitwise_equal, both_zero),
      not_exprt(nan));
  }
  else
    assert(0);
    
  // not reached
  return false_exprt();
}

/*******************************************************************\

Function: float_bvt::isinf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::isinf(
  const exprt &src,
  const ieee_float_spect &spec)
{
  return and_exprt(
    exponent_all_ones(src, spec),
    fraction_all_zeros(src, spec));
}

/*******************************************************************\

Function: float_bvt::isfinite

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::isfinite(
  const exprt &src,
  const ieee_float_spect &spec)
{
  return not_exprt(or_exprt(isinf(src, spec), isnan(src, spec)));
}

/*******************************************************************\

Function: float_bvt::get_exponent

  Inputs:

 Outputs:

 Purpose: Gets the unbiased exponent in a floating-point bit-vector

\*******************************************************************/

exprt float_bvt::get_exponent(
  const exprt &src,
  const ieee_float_spect &spec)
{
  return extractbits_exprt(
    src, spec.f+spec.e-1, spec.f,
    unsignedbv_typet(spec.e));
}

/*******************************************************************\

Function: float_bvt::get_fraction

  Inputs:

 Outputs:

 Purpose: Gets the fraction without hidden bit in a floating-point
          bit-vector src

\*******************************************************************/

exprt float_bvt::get_fraction(
  const exprt &src,
  const ieee_float_spect &spec)
{
  return extractbits_exprt(
    src, spec.f-1, 0,
    unsignedbv_typet(spec.f));
}

/*******************************************************************\

Function: float_bvt::isnan

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::isnan(
  const exprt &src,
  const ieee_float_spect &spec)
{
  return and_exprt(exponent_all_ones(src, spec),
                   not_exprt(fraction_all_zeros(src, spec)));
}

/*******************************************************************\

Function: float_bvt::normalization_shift

  Inputs:

 Outputs:

 Purpose: normalize fraction/exponent pair
          returns 'zero' if fraction is zero

\*******************************************************************/

void float_bvt::normalization_shift(
  exprt &fraction,
  exprt &exponent)
{
  // n-log-n alignment shifter.
  // The worst-case shift is the number of fraction
  // bits minus one, in case the faction is one exactly.
  unsigned fraction_bits=to_unsignedbv_type(fraction.type()).get_width();
  unsigned exponent_bits=to_signedbv_type(exponent.type()).get_width();
  assert(fraction_bits!=0);  
  
  unsigned depth=integer2unsigned(address_bits(fraction_bits-1));
  
  if(exponent_bits<depth)
    exponent=typecast_exprt(exponent, signedbv_typet(depth));

  exprt exponent_delta=gen_zero(exponent.type());
  
  for(int d=depth-1; d>=0; d--)
  {
    unsigned distance=(1<<d);
    assert(fraction_bits>distance);
    
    // check if first 'distance'-many bits are zeros
    const exprt prefix=
      extractbits_exprt(fraction, fraction_bits-1, fraction_bits-distance,
                        unsignedbv_typet(distance));
    exprt prefix_is_zero=equal_exprt(prefix, gen_zero(prefix.type()));
    
    // If so, shift the zeros out left by 'distance'.
    // Otherwise, leave as is.
    const exprt shifted=
      shl_exprt(fraction, distance);
    
    fraction=
      if_exprt(prefix_is_zero, shifted, fraction);
      
    // add corresponding weight to exponent
    assert(d<(signed int)exponent_bits);

    exponent_delta=
      bitor_exprt(exponent_delta,
        shl_exprt(typecast_exprt(prefix_is_zero, exponent_delta.type()), d));
  }  
    
  exponent=minus_exprt(exponent, exponent_delta);
}

/*******************************************************************\

Function: float_bvt::denormalization_shift

  Inputs:

 Outputs:

 Purpose: make sure exponent is not too small;
          the exponent is unbiased

\*******************************************************************/

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
  
  unsigned exponent_bits=to_signedbv_type(exponent.type()).get_width();
  assert(exponent_bits>=spec.e);

#if 1
  // Need to sign extend to avoid overflow.  Note that this is a
  // relatively rare problem as the value needs to be close to the top
  // of the exponent range and then range must not have been
  // previously extended as add, multiply, etc. do.  This is primarily
  // to handle casting down from larger ranges.
  exponent=typecast_exprt(exponent, signedbv_typet(exponent_bits+1));
#endif

  exprt distance=minus_exprt(
    from_integer(-bias+1, exponent.type()), exponent);

  // use sign bit
  exprt denormal=and_exprt(
    not_exprt(sign_exprt(distance)),
    notequal_exprt(distance, gen_zero(distance.type())));

#if 1
  // Care must be taken to not loose information required for the
  // guard and sticky bits.  +3 is for the hidden, guard and sticky bits.
  unsigned fraction_bits=to_unsignedbv_type(fraction.type()).get_width();
  
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

/*******************************************************************\

Function: float_bvt::rounder

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::rounder(
  const unbiased_floatt &src,
  const exprt &rm,
  const ieee_float_spect &spec)
{
  // incoming: some fraction (with explicit 1),
  //           some exponent without bias
  // outgoing: rounded, with right size, with hidden bit, bias
  
  exprt aligned_fraction=src.fraction,
        aligned_exponent=src.exponent;

  {
    unsigned exponent_bits=
      std::max((unsigned long)integer2long(address_bits(spec.f)),
               (unsigned long)spec.e)+1;

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

/*******************************************************************\

Function: float_bvt::fraction_rounding_decision

  Inputs:

 Outputs:

 Purpose: rounding decision for fraction using sticky bit

\*******************************************************************/

exprt float_bvt::fraction_rounding_decision(
  const unsigned dest_bits,
  const exprt sign,
  const exprt &fraction,
  const rounding_mode_bitst &rounding_mode_bits)
{
  unsigned fraction_bits=
    to_unsignedbv_type(fraction.type()).get_width();

  assert(dest_bits<fraction_bits);

  // we have too many fraction bits
  unsigned extra_bits=fraction_bits-dest_bits;

  // more than two extra bits are superflus, and are
  // turned into a sticky bit

  exprt sticky_bit=false_exprt();

  if(extra_bits>=2)
  {
    // We keep most-significant bits, and thus the tail is made
    // of least-significant bits.
    exprt tail=
      extractbits_exprt(fraction, extra_bits-2, 0,
                        unsignedbv_typet(extra_bits-2+1));
    sticky_bit=notequal_exprt(tail, gen_zero(tail.type()));
  }

  // the rounding bit is the last extra bit
  assert(extra_bits>=1);
  exprt rounding_bit=extractbit_exprt(fraction, extra_bits-1);

  // we get one bit of the fraction for some rounding decisions
  exprt rounding_least=extractbit_exprt(fraction, extra_bits);

  // round-to-nearest (ties to even)
  exprt round_to_even=
    and_exprt(rounding_bit,
              or_exprt(rounding_least, sticky_bit));
  
  // round up
  exprt round_to_plus_inf=
    and_exprt(not_exprt(sign),
              or_exprt(rounding_bit, sticky_bit));

  // round down
  exprt round_to_minus_inf=
    and_exprt(sign,
              or_exprt(rounding_bit, sticky_bit));

  // round to zero
  exprt round_to_zero=
    false_exprt();

  // now select appropriate one
  return if_exprt(rounding_mode_bits.round_to_even, round_to_even,
         if_exprt(rounding_mode_bits.round_to_plus_inf, round_to_plus_inf,
         if_exprt(rounding_mode_bits.round_to_minus_inf, round_to_minus_inf,
         if_exprt(rounding_mode_bits.round_to_zero, round_to_zero,
           false_exprt())))); // otherwise zero
}                

/*******************************************************************\

Function: float_bvt::round_fraction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void float_bvt::round_fraction(
  unbiased_floatt &result,
  const rounding_mode_bitst &rounding_mode_bits,
  const ieee_float_spect &spec)
{
  unsigned fraction_size=spec.f+1;
  unsigned result_fraction_size=
    to_unsignedbv_type(result.fraction.type()).get_width();

  // do we need to enlarge the fraction?
  if(result_fraction_size<fraction_size)
  {
    // pad with zeros at bottom
    unsigned padding=fraction_size-result_fraction_size;

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
    unsigned extra_bits=result_fraction_size-fraction_size;
    assert(extra_bits>=1);

    // this computes the rounding decision    
    exprt increment=fraction_rounding_decision(
      fraction_size, result.sign, result.fraction, rounding_mode_bits);

    // chop off all the extra bits
    result.fraction=extractbits_exprt(
      result.fraction, result_fraction_size-1, extra_bits,
      unsignedbv_typet(fraction_size));

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
    exprt new_integer_part=or_exprt(integer_part1, integer_part0);

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
    exprt oldMSB=
      extractbit_exprt(result.fraction, fraction_size-1);

    // increment if 'increment' is true
    result.fraction=
      plus_exprt(result.fraction,
                 typecast_exprt(increment, result.fraction.type()));

    // Normal overflow when old MSB == 1 and new MSB == 0
    exprt newMSB=
      extractbit_exprt(result.fraction, fraction_size-1);
    
    exprt overflow=and_exprt(oldMSB, not_exprt(newMSB));

    // Subnormal to normal transition when old MSB == 0 and new MSB == 1
    exprt subnormal_to_normal=
      and_exprt(not_exprt(oldMSB), newMSB);

    // In case of an overflow or subnormal to normal conversion,
    // the exponent has to be incremented.
    result.exponent=
      plus_exprt(result.exponent, 
                 if_exprt(or_exprt(overflow, subnormal_to_normal), 
                          gen_one(result.exponent.type()),
                          gen_zero(result.exponent.type())));

    // post normalization of the fraction
    // In the case of overflow, set the MSB to 1
    // The subnormal case will have (only) the MSB set to 1
    result.fraction=bitor_exprt(
      result.fraction,
      if_exprt(overflow,
               from_integer(1<<(fraction_size-1), result.fraction.type()),
               gen_zero(result.fraction.type())));
#endif
  }
}

/*******************************************************************\

Function: float_bvt::round_exponent

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void float_bvt::round_exponent(
  unbiased_floatt &result,
  const rounding_mode_bitst &rounding_mode_bits,
  const ieee_float_spect &spec)
{
  unsigned result_exponent_size=
    to_signedbv_type(result.exponent.type()).get_width();

  // do we need to enlarge the exponent?
  if(result_exponent_size<spec.e)
  {
    // should have been done before
    assert(false);
  }
  else if(result_exponent_size==spec.e) // it stays
  {
    // do nothing
  }
  else // exponent gets smaller -- chop off top bits
  {
    exprt old_exponent=result.exponent;
    result.exponent=
      extractbits_exprt(result.exponent, spec.e-1, 0, signedbv_typet(spec.e));

    // max_exponent is the maximum representable
    // i.e. 1 higher than the maximum possible for a normal number
    exprt max_exponent=
      from_integer(
        spec.max_exponent()-spec.bias(), old_exponent.type());

    // the exponent is garbage if the fractional is zero

    exprt exponent_too_large=
      and_exprt(
        binary_relation_exprt(old_exponent, ID_ge, max_exponent),
        notequal_exprt(result.fraction, gen_zero(result.fraction.type())));

#if 1
    // Directed rounding modes round overflow to the maximum normal
    // depending on the particular mode and the sign
    exprt overflow_to_inf=
      or_exprt(rounding_mode_bits.round_to_even,
      or_exprt(and_exprt(rounding_mode_bits.round_to_plus_inf,
                         not_exprt(result.sign)),
               and_exprt(rounding_mode_bits.round_to_minus_inf,
                         result.sign)));

    exprt set_to_max=
      and_exprt(exponent_too_large, not_exprt(overflow_to_inf));


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

/*******************************************************************\

Function: float_bvt::bias

  Inputs:

 Outputs:

 Purpose: takes an unbiased float, and applies the bias

\*******************************************************************/

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
  assert(to_unsignedbv_type(src.fraction.type()).get_width()==spec.f+1);

  exprt hidden_bit=extractbit_exprt(src.fraction, spec.f);
  exprt denormal=not_exprt(hidden_bit);

  result.fraction=
    extractbits_exprt(
      src.fraction, spec.f-1, 0,
      unsignedbv_typet(spec.f));

  // make exponent zero if its denormal
  // (includes zero)
  result.exponent=
    if_exprt(denormal, from_integer(0, result.exponent.type()),
             result.exponent);

  return result;
}

/*******************************************************************\

Function: float_bvt::add_bias

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::add_bias(
  const exprt &src,
  const ieee_float_spect &spec)
{
  typet t=unsignedbv_typet(spec.e);
  return plus_exprt(
    typecast_exprt(src, t),
    from_integer(spec.bias(), t));
}

/*******************************************************************\

Function: float_bvt::sub_bias

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::sub_bias(
  const exprt &src,
  const ieee_float_spect &spec)
{
  typet t=signedbv_typet(spec.e);
  return minus_exprt(
    typecast_exprt(src, t),
    from_integer(spec.bias(), t));
}

/*******************************************************************\

Function: float_bvt::unpack

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
  result.zero=is_zero(src, spec);
  result.NaN=isnan(src, spec);

  return result;
}

/*******************************************************************\

Function: float_bvt::pack

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::pack(
  const biased_floatt &src,
  const ieee_float_spect &spec)
{
  assert(to_unsignedbv_type(src.fraction.type()).get_width()==spec.f);
  assert(to_unsignedbv_type(src.exponent.type()).get_width()==spec.e);

  // do sign -- we make this 'false' for NaN
  exprt sign_bit=
    if_exprt(src.NaN, false_exprt(), src.sign);

  // the fraction is zero in case of infinity,
  // and one in case of NaN
  exprt fraction=
    if_exprt(src.NaN, from_integer(1, src.fraction.type()),
    if_exprt(src.infinity, from_integer(0, src.fraction.type()),
    src.fraction));

  exprt infinity_or_NaN=
    or_exprt(src.NaN, src.infinity);

  // do exponent
  exprt exponent=
    if_exprt(infinity_or_NaN, from_integer(-1, src.exponent.type()),
             src.exponent);

  // stitch all three together
  return concatenation_exprt(
    sign_bit,
      concatenation_exprt(
      exponent, fraction,
      unsignedbv_typet(spec.e+spec.f)),
    spec.to_type());
}

/*******************************************************************\

Function: float_bvt::sticky_right_shift

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::sticky_right_shift(
  const exprt &op,
  const exprt &dist,
  exprt &sticky)
{
  unsigned d=1, width=to_unsignedbv_type(op.type()).get_width();
  exprt result=op;
  sticky=false_exprt();

  unsigned dist_width=to_bitvector_type(dist.type()).get_width();

  for(unsigned stage=0; stage<dist_width; stage++)
  {
    exprt tmp=lshr_exprt(result, d);

    exprt lost_bits;

    if(d<=width)
      lost_bits=extractbits_exprt(result, d-1, 0, unsignedbv_typet(d));
    else
      lost_bits=result;

    exprt dist_bit=
      extractbit_exprt(dist, stage);

    sticky=or_exprt(
        and_exprt(dist_bit,
                  notequal_exprt(lost_bits, gen_zero(lost_bits.type()))),
        sticky);

    result=if_exprt(dist_bit, tmp, result);

    d=d<<1;
  }

  return result;
}
