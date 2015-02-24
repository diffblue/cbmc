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
    if(expr.type().id()==ID_signedbv)
      return to_signed_integer(
        expr.op0(), to_signedbv_type(expr.type()).get_width(), expr.op1(), get_spec(expr.op0()));
    else if(expr.type().id()==ID_unsignedbv)
      return to_unsigned_integer(
        expr.op0(), to_unsignedbv_type(expr.type()).get_width(), expr.op1(), get_spec(expr.op0()));
    else if(expr.op0().type().id()==ID_signedbv)
      return from_signed_integer(
        expr.op0(), expr.op1(), get_spec(expr));
    else if(expr.op0().type().id()==ID_unsignedbv)
      return from_unsigned_integer(
        expr.op0(), expr.op1(), get_spec(expr));
    else
      return conversion(expr.op0(), expr.op1(), get_spec(expr.op0()), get_spec(expr));
  }
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
  else
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
  exprt round_to_even=from_integer(ieee_floatt::ROUND_TO_EVEN, rm.type());
  exprt round_to_plus_inf=from_integer(ieee_floatt::ROUND_TO_PLUS_INF, rm.type());
  exprt round_to_minus_inf=from_integer(ieee_floatt::ROUND_TO_MINUS_INF, rm.type());
  exprt round_to_zero=from_integer(ieee_floatt::ROUND_TO_ZERO, rm.type());

  round_to_even=equal_exprt(rm, round_to_even);
  round_to_plus_inf=equal_exprt(rm, round_to_plus_inf);
  round_to_minus_inf=equal_exprt(rm, round_to_minus_inf);
  round_to_zero=equal_exprt(rm, round_to_zero);
}

/*******************************************************************\

Function: float_bvt::sign_bit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::sign_bit(
  const exprt &op,
  const ieee_float_spect &spec)
{
  return extractbit_exprt(op, uint_const(spec.width()-1));
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
  unbiased_floatt result;

  // we need to adjust for negative integers
  result.sign=sign_bit(src, spec);

  result.fraction=abs_exprt(src);
  
  unsigned src_width=to_signedbv_type(src.type()).get_width();

  // build an exponent (unbiased) -- this is signed!
  result.exponent=
    from_integer(
      src_width-1,
      signedbv_typet(address_bits(src_width-1).to_long()+1));

  return rounder(result);
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

  unsigned src_width=to_signedbv_type(src.type()).get_width();

  // build an exponent (unbiased) -- this is signed!
  result.exponent=
    from_integer(
      src_width-1,
      signedbv_typet(address_bits(src_width-1).to_long()+1));

  result.sign=false_exprt();

  return rounder(result);
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
  #if 0
  const unbiased_floatt unpacked=unpack(src, spec);
  
  rounding_mode_bitst rounding_mode_bits(rm);

  // The following is the usual case in ANSI-C, and we optimize for that.
  if(rounding_mode_bits.round_to_zero.is_true())
  {
    // if the exponent is positive, shift right
    exprt offset=from_integer(spec.f, signedbv_typet(spec.e));
    exprt distance=minus_exprt(offset, unpacked.exponent);
    exprt shift_result=lshr_exprt(unpacked.fraction, distance);

    // if the exponent is negative, we have zero anyways
    exprt result=shift_result;
    exprt exponent_sign=unpacked.exponent[unpacked.exponent.size()-1];

    for(unsigned i=0; i<result.size(); i++)
      result[i]=and_exprt(result[i],
                          not_exprt(exponent_sign));

    // chop out the right number of bits from the result
    typet result_type=
      is_signed?signedbv_typet(dest_width):
                unsignedbv_typet(dest_width);
    
    result=typecast_exprt(result, result_type);

    // if signed, apply sign.
    if(is_signed)
    {
      result=bv_utils.cond_negate(result, unpacked.sign);
    }
    else
    {
      // It's unclear what the behaviour for negative floats
      // to integer shall be.
    }

    return result;
  }
  else
    assert(0);
  #endif
}

/*******************************************************************\

Function: float_bvt::build_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
exprt float_bvt::build_constant(const ieee_floatt &src)
{
  unbiased_floatt result;

  result.sign=const_literal(src.get_sign());
  result.NaN=const_literal(src.is_NaN());
  result.infinity=const_literal(src.is_infinity());
  result.exponent=bv_utils.build_constant(src.get_exponent(), spec.e);
  result.fraction=bv_utils.build_constant(src.get_fraction(), spec.f+1);

  return pack(bias(result));
}
#endif

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
  #if 0
  #if 1
  // Catch the special case in which we extend,
  // e.g. single to double.
  // In this case, rounding can be avoided,
  // but a denormal number may be come normal.
  // Be careful to exclude the difficult case
  // when denormalised numbers in the old format
  // can be converted to denormalised numbers in the
  // new format.  Note that this is rare and will only
  // happen with very non-standard formats.
 
  int sourceSmallestNormalExponent = -((1 << (spec.e - 1)) - 1);
  int sourceSmallestDenormalExponent = 
    sourceSmallestNormalExponent - spec.f;

  // Using the fact that f doesn't include the hidden bit
   
  int destSmallestNormalExponent = -((1 << (dest_spec.e - 1)) - 1);

  if(dest_spec.e>=spec.e &&
     dest_spec.f>=spec.f &&
     !(sourceSmallestDenormalExponent < destSmallestNormalExponent))
  {
    unbiased_floatt unpacked_src=unpack(src);
    unbiased_floatt result;
    
    // the fraction gets zero-padded
    unsigned padding=dest_spec.f-spec.f;
    result.fraction=
      bv_utils.concatenate(bv_utils.zeros(padding), unpacked_src.fraction);
    
    // the exponent gets sign-extended
    result.exponent=
      bv_utils.sign_extension(unpacked_src.exponent, dest_spec.e);

    // if the number was denormal and is normal in the new format,
    // normalise it!
    if(dest_spec.e > spec.e)
    {
      normalization_shift(result.fraction,result.exponent);	
    }

    // the flags get copied
    result.sign=unpacked_src.sign;
    result.NaN=unpacked_src.NaN;
    result.infinity=unpacked_src.infinity;

    // no rounding needed!
    spec=dest_spec; 
    return pack(bias(result));
  }
  else
  #endif
  {
    // we actually need to round
    unbiased_floatt result=unpack(src);
    spec=dest_spec;
    return rounder(result);
  }
  #endif
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
  #if 0
  // extend both
  exprt extended_exponent1=bv_utils.sign_extension(src1.exponent, src1.exponent.size()+1);
  exprt extended_exponent2=bv_utils.sign_extension(src2.exponent, src2.exponent.size()+1);

  assert(extended_exponent1.size()==extended_exponent2.size());

  // compute shift distance (here is the subtraction)
  return bv_utils.sub(extended_exponent1, extended_exponent2);
  #endif
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
  #if 0
  unbiased_floatt unpacked1=unpack(op0, spec);
  unbiased_floatt unpacked2=unpack(op1, spec);

  // subtract?
  if(subtract)
    unpacked2.sign=not_exprt(unpacked2.sign);

  // figure out which operand has the bigger exponent
  const exprt exponent_difference=subtract_exponents(unpacked1, unpacked2);
  exprt src2_bigger=exponent_difference.back();

  const exprt bigger_exponent=
    if_exprt(src2_bigger, unpacked2.exponent, unpacked1.exponent);

  // swap fractions as needed
  const exprt new_fraction1=
    if_exprt(src2_bigger, unpacked2.fraction, unpacked1.fraction);

  const exprt new_fraction2=
    if_exprt(src2_bigger, unpacked1.fraction, unpacked2.fraction);

  // compute distance
  const exprt distance=bv_utils.absolute_value(exponent_difference);

  // limit the distance: shifting more than f+3 bits is unnecessary
  const exprt limited_dist=limit_distance(distance, spec.f+3);

  // pad fractions with 2 zeros from below
  const exprt fraction1_padded=bv_utils.concatenate(bv_utils.zeros(3), new_fraction1);
  const exprt fraction2_padded=bv_utils.concatenate(bv_utils.zeros(3), new_fraction2);

  // shift new_fraction2
  exprt sticky_bit;
  const exprt fraction1_shifted=fraction1_padded;
  const exprt fraction2_shifted=sticky_right_shift(
    fraction2_padded, bv_utilst::LRIGHT, limited_dist, sticky_bit);

  // sticky bit: or of the bits lost by the right-shift
  exprt fraction2_stickied=fraction2_shifted;
  fraction2_stickied[0]=or_exprt(fraction2_shifted[0], sticky_bit);

  // need to have two extra fraction bits for addition and rounding
  const exprt fraction1_ext=bv_utils.zero_extension(fraction1_shifted, fraction1_shifted.size()+2);
  const exprt fraction2_ext=bv_utils.zero_extension(fraction2_stickied, fraction2_stickied.size()+2);

  unbiased_floatt result;

  // now add/sub them
  exprt subtract_lit=xor_exprt(unpacked1.sign, unpacked2.sign);
  result.fraction=
    bv_utils.add_sub(fraction1_ext, fraction2_ext, subtract_lit);

  // sign of result
  exprt fraction_sign=result.fraction.back();
  result.fraction=bv_utils.absolute_value(result.fraction);

  result.exponent=bigger_exponent;

  // adjust the exponent for the fact that we added two bits to the fraction
  result.exponent=
    plus_exprt(bv_utils.sign_extension(result.exponent, result.exponent.size()+1),
      bv_utils.build_constant(2, result.exponent.size()+1));

  // NaN?
  result.NaN=or_exprt(
      and_exprt(and_exprt(unpacked1.infinity, unpacked2.infinity),
                prop.lxor(unpacked1.sign, unpacked2.sign)),
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
      not_exprt(or_exprt(result.fraction)));

  // sign
  exprt add_sub_sign=
    prop.lxor(if_exprt(src2_bigger, unpacked2.sign, unpacked1.sign),
              fraction_sign);

  exprt infinity_sign=
    if_exprt(unpacked1.infinity, unpacked1.sign, unpacked2.sign);

  #if 1
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

  return rounder(result);
  #endif
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
  #if 0
  unsigned nb_bits=integer2unsigned(address_bits(limit));

  exprt upper_bits=dist;
  upper_bits.erase(upper_bits.begin(), upper_bits.begin()+nb_bits);
  exprt or_upper_bits=prop.lor(upper_bits);

  exprt lower_bits=dist;
  lower_bits.resize(nb_bits);

  exprt result;
  result.resize(lower_bits.size());

  // bitwise or with or_upper_bits
  for(unsigned int i=0; i<result.size(); i++)
    result[i]=prop.lor(lower_bits[i], or_upper_bits);

  return result;
  #endif
}

/*******************************************************************\

Function: float_bvt::mul

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::mul(
  const exprt &op0,
  const exprt &op1,
  const exprt &rm,
  const ieee_float_spect &spec)
{
  // unpack
  #if 0
  const unbiased_floatt unpacked1=unpack(src1, spec);
  const unbiased_floatt unpacked2=unpack(src2, spec);

  // zero-extend the fractions
  const exprt fraction1=bv_utils.zero_extension(unpacked1.fraction, unpacked1.fraction.size()*2);
  const exprt fraction2=bv_utils.zero_extension(unpacked2.fraction, unpacked2.fraction.size()*2);

  // multiply fractions
  unbiased_floatt result;
  result.fraction=bv_utils.unsigned_multiplier(fraction1, fraction2);

  // extend exponents to account for overflow
  // add two bits, as we do extra arithmetic on it later
  const exprt exponent1=bv_utils.sign_extension(unpacked1.exponent, unpacked1.exponent.size()+2);
  const exprt exponent2=bv_utils.sign_extension(unpacked2.exponent, unpacked2.exponent.size()+2);

  exprt added_exponent=plus_exprt(exponent1, exponent2);

  // adjust, we are thowing in an extra fraction bit
  // it has been extended above
  result.exponent=bv_utils.inc(added_exponent);

  // new sign
  result.sign=xor_exprt(unpacked1.sign, unpacked2.sign);

  // infinity?
  result.infinity=or_exprt(unpacked1.infinity, unpacked2.infinity);

  // NaN?
  {
    exprt NaN_cond(ID_or, bool_typet());

    NaN_cond.copy_to_operands(is_NaN(src1));
    NaN_cond.copy_to_operands(is_NaN(src2));

    // infinity * 0 is NaN!
    NaN_cond.copy_to_operands(and_exprt(is_zero(src1), unpacked2.infinity));
    NaN_cond.copy_to_operands(and_exprt(is_zero(src2), unpacked1.infinity));

    result.NaN=or_exprt(NaN_cond);
  }

  return rounder(result);
  #endif
}

/*******************************************************************\

Function: float_bvt::div

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::div(
  const exprt &op0,
  const exprt &op1,
  const exprt &rm,
  const ieee_float_spect &spec)
{
  // unpack
  #if 0
  const unbiased_floatt unpacked1=unpack(src1, spec);
  const unbiased_floatt unpacked2=unpack(src2, spec);
  
  unsigned div_width=unpacked1.fraction.size()*2+1;

  // pad fraction1 with zeros
  exprt fraction1=unpacked1.fraction;
  fraction1.reserve(div_width);
  while(fraction1.size()<div_width)
    fraction1.insert(fraction1.begin(), const_literal(false));

  // zero-extend fraction2
  const exprt fraction2=
    bv_utils.zero_extension(unpacked2.fraction, div_width);

  // divide fractions
  unbiased_floatt result;
  exprt rem;
  bv_utils.unsigned_divider(fraction1, fraction2, result.fraction, rem);
  
  // is there a remainder?
  exprt have_remainder=bv_utils.is_not_zero(rem);
  
  // we throw this into the result, as one additional bit,
  // to get the right rounding decision
  result.fraction.insert(
    result.fraction.begin(), have_remainder);
    
  // We will subtract the exponents;
  // to account for overflow, we add a bit.
  const exprt exponent1=bv_utils.sign_extension(unpacked1.exponent, unpacked1.exponent.size()+1);
  const exprt exponent2=bv_utils.sign_extension(unpacked2.exponent, unpacked2.exponent.size()+1);

  // subtract exponents
  exprt added_exponent=bv_utils.sub(exponent1, exponent2);

  // adjust, as we have thown in extra fraction bits
  result.exponent=bv_utils.add(
    added_exponent,
    bv_utils.build_constant(spec.f, added_exponent.size()));

  // new sign
  result.sign=prop.lxor(unpacked1.sign, unpacked2.sign);

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
  
  result.fraction=bv_utils.select(force_zero,
    bv_utils.zeros(result.fraction.size()), result.fraction);

  return rounder(result);
  #endif
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
      notequal_exprt(sign_bit(src1, spec), sign_bit(src2, spec));

    // as long as the signs match: compare like unsigned numbers

    // this works due to the BIAS
    exprt less_than1=
      binary_relation_exprt(
        typecast_exprt(src1, unsignedbv_typet(spec.width())),
        ID_lt,
        typecast_exprt(src2, unsignedbv_typet(spec.width())));

    // if both are negative (and not the same), need to turn around!
    exprt less_than2=
        notequal_exprt(less_than1,
                       and_exprt(sign_bit(src1, spec), sign_bit(src2, spec)));

    exprt less_than3=
      if_exprt(signs_different,
        sign_bit(src1, spec),
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
    src, uint_const(spec.f+spec.e-1), uint_const(spec.f),
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
    src, uint_const(spec.f-1), uint_const(0),
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

void float_bvt::normalization_shift(exprt &fraction, exprt &exponent)
{
  #if 0
  #if 0
  // this thing is quadratic!

  exprt new_fraction=prop.new_variables(fraction.size());
  exprt new_exponent=prop.new_variables(exponent.size());

  // i is the shift distance
  for(unsigned i=0; i<fraction.size(); i++)
  {
    exprt equal;

    // the bits above need to be zero
    for(unsigned j=0; j<i; j++)
      equal.push_back(
        not_exprt(fraction[fraction.size()-1-j]));

    // this one needs to be one
    equal.push_back(fraction[fraction.size()-1-i]);

    // iff all of that holds, we shift here!
    exprt shift=and_exprt(equal);

    // build shifted value
    exprt shifted_fraction=bv_utils.shift(fraction, bv_utilst::LEFT, i);
    bv_utils.cond_implies_equal(shift, shifted_fraction, new_fraction);

    // build new exponent
    exprt adjustment=bv_utils.build_constant(-i, exponent.size());
    exprt added_exponent=bv_utils.add(exponent, adjustment);
    bv_utils.cond_implies_equal(shift, added_exponent, new_exponent);
  }

  // Fraction all zero? It stays zero.
  // The exponent is undefined in that case.
  exprt fraction_all_zero=bv_utils.is_zero(fraction);
  exprt zero_fraction;
  zero_fraction.resize(fraction.size(), const_literal(false));
  bv_utils.cond_implies_equal(fraction_all_zero, zero_fraction, new_fraction);
  
  fraction=new_fraction;
  exponent=new_exponent;

  #else

  // n-log-n alignment shifter.
  // The worst-case shift is the number of fraction
  // bits minus one, in case the faction is one exactly.
  assert(!fraction.empty());  
  unsigned depth=integer2unsigned(address_bits(fraction.size()-1));
  
  if(exponent.size()<depth)
    exponent=bv_utils.sign_extension(exponent, depth);
  
  exprt exponent_delta=bv_utils.zeros(exponent.size());
  
  for(int d=depth-1; d>=0; d--)
  {
    unsigned distance=(1<<d);
    assert(fraction.size()>distance);
    
    // check if first 'distance'-many bits are zeros
    const exprt prefix=bv_utils.extract_msb(fraction, distance);
    exprt prefix_is_zero=bv_utils.is_zero(prefix);
    
    // If so, shift the zeros out left by 'distance'.
    // Otherwise, leave as is.
    const exprt shifted=
      bv_utils.shift(fraction, bv_utilst::LEFT, distance);
    
    fraction=
      bv_utils.select(prefix_is_zero, shifted, fraction);
      
    // add corresponding weight to exponent
    assert(d<(signed)exponent_delta.size());
    exponent_delta[d]=prefix_is_zero;
  }  
    
  exponent=bv_utils.sub(exponent, exponent_delta);
  
  #endif
  #endif
}

/*******************************************************************\

Function: float_bvt::denormalization_shift

  Inputs:

 Outputs:

 Purpose: make sure exponent is not too small;
          the exponent is unbiased

\*******************************************************************/

void float_bvt::denormalization_shift(exprt &fraction, exprt &exponent)
{
  #if 0
  mp_integer bias=spec.bias();

  // Is the exponent strictly less than -bias+1, i.e., exponent<-bias+1?
  // This is transformed to distance=(-bias+1)-exponent
  // i.e., distance>0
  // Note that 1-bias is the exponent represented by 0...01,
  // i.e. the exponent of the smallest normal number and thus the 'base'
  // exponent for subnormal numbers.
  
  assert(exponent.size()>=spec.e);

#if 1
  // Need to sign extend to avoid overflow.  Note that this is a
  // relatively rare problem as the value needs to be close to the top
  // of the exponent range and then range must not have been
  // previously extended as add, multiply, etc. do.  This is primarily
  // to handle casting down from larger ranges.
  exponent = bv_utils.sign_extension(exponent, exponent.size() + 1);
#endif

  exprt distance=bv_utils.sub(
    bv_utils.build_constant(-bias+1, exponent.size()), exponent);

  // use sign bit
  exprt denormal=and_exprt(
    not_exprt(distance.back()),
    not_exprt(bv_utils.is_zero(distance)));

#if 1
  // Care must be taken to not loose information required for the
  // guard and sticky bits.  +3 is for the hidden, guard and sticky bits.
  if (fraction.size() < (spec.f + 3)) 
  { 
    // Add zeros at the LSB end for the guard bit to shift into
    fraction=
      bv_utils.concatenate(bv_utils.zeros((spec.f + 3) - fraction.size()),
			   fraction);
  }

  exprt denormalisedFraction = fraction;

  exprt sticky_bit = const_literal(false);
  denormalisedFraction = 
    sticky_right_shift(fraction, bv_utilst::LRIGHT, distance, sticky_bit);
  denormalisedFraction[0] = or_exprt(denormalisedFraction[0], sticky_bit);

  fraction=
    bv_utils.select(
      denormal,
      denormalisedFraction,
      fraction);

#else
  fraction=
    bv_utils.select(
      denormal,
      bv_utils.shift(fraction, bv_utilst::LRIGHT, distance),
      fraction);
#endif

  exponent=
    bv_utils.select(denormal,
      bv_utils.build_constant(-bias, exponent.size()),
      exponent);
  #endif
}

/*******************************************************************\

Function: float_bvt::rounder

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::rounder(const unbiased_floatt &src)
{
  #if 0
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
    if(aligned_exponent.size()<exponent_bits)
    {
      // sign extend
      aligned_exponent=
        bv_utils.sign_extension(aligned_exponent, exponent_bits);
    }
  }

  // align it!
  normalization_shift(aligned_fraction, aligned_exponent);
  denormalization_shift(aligned_fraction, aligned_exponent);

  unbiased_floatt result;
  result.fraction=aligned_fraction;
  result.exponent=aligned_exponent;
  result.sign=src.sign;
  result.NaN=src.NaN;
  result.infinity=src.infinity;

  round_fraction(result);
  round_exponent(result);

  return pack(bias(result));
  #endif
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
  const exprt &fraction)
{
  #if 0
  assert(dest_bits<fraction.size());

  // we have too many fraction bits
  unsigned extra_bits=fraction.size()-dest_bits;

  // more than two extra bits are superflus, and are
  // turned into a sticky bit

  exprt sticky_bit=const_literal(false);

  if(extra_bits>=2)
  {
    // We keep most-significant bits, and thus the tail is made
    // of least-significant bits.
    exprt tail=bv_utils.extract(fraction, 0, extra_bits-2);
    sticky_bit=or_exprt(tail);
  }

  // the rounding bit is the last extra bit
  assert(extra_bits>=1);
  exprt rounding_bit=fraction[extra_bits-1];

  // we get one bit of the fraction for some rounding decisions
  exprt rounding_least=fraction[extra_bits];

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
    const_literal(false);

  // now select appropriate one
  return if_exprt(rounding_mode_bits.round_to_even, round_to_even,
         if_exprt(rounding_mode_bits.round_to_plus_inf, round_to_plus_inf,
         if_exprt(rounding_mode_bits.round_to_minus_inf, round_to_minus_inf,
         if_exprt(rounding_mode_bits.round_to_zero, round_to_zero,
           prop.new_variable())))); // otherwise non-det
  #endif
}                

/*******************************************************************\

Function: float_bvt::round_fraction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void float_bvt::round_fraction(unbiased_floatt &result)
{
  #if 0
  unsigned fraction_size=spec.f+1;

  // do we need to enlarge the fraction?
  if(result.fraction.size()<fraction_size)
  {
    // pad with zeros at bottom
    unsigned padding=fraction_size-result.fraction.size();

    result.fraction=bv_utils.concatenate(
      bv_utils.zeros(padding),
      result.fraction);

    assert(result.fraction.size()==fraction_size);
  }
  else if(result.fraction.size()==fraction_size) // it stays
  {
    // do nothing
  }
  else // fraction gets smaller -- rounding
  {
    unsigned extra_bits=result.fraction.size()-fraction_size;
    assert(extra_bits>=1);

    // this computes the rounding decision    
    exprt increment=fraction_rounding_decision(
      fraction_size, result.sign, result.fraction);

    // chop off all the extra bits
    result.fraction=bv_utils.extract(
      result.fraction, extra_bits, result.fraction.size()-1);

    assert(result.fraction.size()==fraction_size);

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
    exprt oldMSB = result.fraction.back();

    result.fraction=bv_utils.incrementer(result.fraction, increment);

    // Normal overflow when old MSB == 1 and new MSB == 0
    exprt overflow=and_exprt(oldMSB, neg(result.fraction.back()));

    // Subnormal to normal transition when old MSB == 0 and new MSB == 1
    exprt subnormal_to_normal=
      and_exprt(neg(oldMSB), result.fraction.back());

    // In case of an overflow or subnormal to normal conversion,
    // the exponent has to be incremented.
    result.exponent=
      bv_utils.incrementer(result.exponent, 
			   or_exprt(overflow, subnormal_to_normal));

    // post normalization of the fraction
    // In the case of overflow, set the MSB to 1
    // The subnormal case will have (only) the MSB set to 1
    result.fraction.back() = or_exprt(result.fraction.back(), overflow);
#endif

  }
  #endif
}

/*******************************************************************\

Function: float_bvt::round_exponent

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void float_bvt::round_exponent(unbiased_floatt &result)
{
  #if 0
  // do we need to enlarge the exponent?
  if(result.exponent.size()<spec.e)
  {
    // should have been done before
    assert(false);
  }
  else if(result.exponent.size()==spec.e) // it stays
  {
    // do nothing
  }
  else // exponent gets smaller -- chop off top bits
  {
    exprt old_exponent=result.exponent;
    result.exponent.resize(spec.e);

    // max_exponent is the maximum representable
    // i.e. 1 higher than the maximum possible for a normal number
    exprt max_exponent=
      bv_utils.build_constant(
        spec.max_exponent()-spec.bias(), old_exponent.size());

    // the exponent is garbage if the fractional is zero

    exprt exponent_too_large=
      and_exprt(
        not_exprt(
          bv_utils.signed_less_than(old_exponent, max_exponent)),
        not_exprt(bv_utils.is_zero(result.fraction)));

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
      bv_utils.build_constant(
        spec.max_exponent()-(spec.bias() + 1), result.exponent.size());

    result.exponent=
      bv_utils.select(set_to_max, largest_normal_exponent, result.exponent);

    result.fraction=
      bv_utils.select(set_to_max,
		      bv_utils.inverted(bv_utils.zeros(result.fraction.size())),
		      result.fraction);

    result.infinity=or_exprt(result.infinity, 
			     and_exprt(exponent_too_large,
				       overflow_to_inf));
#else
    result.infinity=or_exprt(result.infinity, exponent_too_large);
#endif
  }
  #endif
}

/*******************************************************************\

Function: float_bvt::bias

  Inputs:

 Outputs:

 Purpose: takes an unbiased float, and applies the bias

\*******************************************************************/

float_bvt::biased_floatt float_bvt::bias(const unbiased_floatt &src)
{
  #if 0
  biased_floatt result;

  result.sign=src.sign;
  result.NaN=src.NaN;
  result.infinity=src.infinity;

  // we need to bias the new exponent
  result.exponent=add_bias(src.exponent);

  // strip off hidden bit
  assert(src.fraction.size()==spec.f+1);

  exprt hidden_bit=src.fraction[src.fraction.size()-1];
  exprt denormal=not_exprt(hidden_bit);

  result.fraction=src.fraction;
  result.fraction.resize(spec.f);

  // make exponent zero if its denormal
  // (includes zero)
  for(unsigned i=0; i<result.exponent.size(); i++)
    result.exponent[i]=
      and_exprt(result.exponent[i], not_exprt(denormal));

  return result;
  #endif
}

/*******************************************************************\

Function: float_bvt::add_bias

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::add_bias(const exprt &src)
{
  #if 0
  assert(src.size()==spec.e);

  return bv_utils.add(
    src,
    bv_utils.build_constant(spec.bias(), spec.e));
  #endif
}

/*******************************************************************\

Function: float_bvt::sub_bias

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::sub_bias(const exprt &src)
{
  #if 0
  assert(src.size()==spec.e);

  return bv_utils.sub(
    src,
    bv_utils.build_constant(spec.bias(), spec.e));
  #endif
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
  #if 0
  assert(src.size()==spec.width());

  unbiased_floatt result;

  result.sign=sign_bit(src);

  result.fraction=get_fraction(src);
  result.fraction.push_back(is_normal(src)); // add hidden bit

  result.exponent=get_exponent(src);
  assert(result.exponent.size()==spec.e);

  // unbias the exponent
  exprt denormal=bv_utils.is_zero(result.exponent);

  result.exponent=
    bv_utils.select(denormal,
      bv_utils.build_constant(-spec.bias()+1, spec.e),
      sub_bias(result.exponent));

  result.infinity=is_infinity(src);
  result.zero=is_zero(src);
  result.NaN=is_NaN(src);

  return result;
  #endif
}

/*******************************************************************\

Function: float_bvt::pack

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::pack(const biased_floatt &src)
{
  #if 0
  assert(src.fraction.size()==spec.f);
  assert(src.exponent.size()==spec.e);

  exprt result;
  result.resize(spec.width());

  // do sign
  // we make this 'false' for NaN
  result[result.size()-1]=
    if_exprt(src.NaN, const_literal(false), src.sign);

  exprt infinity_or_NaN=
    or_exprt(src.NaN, src.infinity);

  // just copy fraction
  for(unsigned i=0; i<spec.f; i++)
    result[i]=and_exprt(src.fraction[i], not_exprt(infinity_or_NaN));

  result[0]=or_exprt(result[0], src.NaN);

  // do exponent
  for(unsigned i=0; i<spec.e; i++)
    result[i+spec.f]=or_exprt(
      src.exponent[i],
      infinity_or_NaN);

  return result;
  #endif
}

/*******************************************************************\

Function: float_bvt::sticky_right_shift

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::sticky_right_shift(
  const exprt &op,
  const bv_utilst::shiftt shift_type,
  const exprt &dist,
  exprt &sticky)
{
  #if 0
  // only right shifts
  assert(shift_type==bv_utilst::LRIGHT ||
         shift_type==bv_utilst::ARIGHT);

  unsigned d=1, width=op.size();
  exprt result=op;
  sticky=false_exprt();

  for(unsigned stage=0; stage<dist.size(); stage++)
  {
    if(dist[stage]!=const_literal(false))
    {
      exprt tmp=bv_utils.shift(result, shift_type, d);

      exprt lost_bits;

      if(d <= result.size())
	lost_bits=bv_utils.extract(result, 0, d-1);
      else
	lost_bits=result;

      sticky=or_exprt(
          and_exprt(dist[stage],or_exprt(lost_bits)),
          sticky);

      for(unsigned i=0; i<width; i++)
        result[i]=if_exprt(dist[stage], tmp[i], result[i]);
    }

    d=d<<1;
  }

  return result;
  #endif
}
