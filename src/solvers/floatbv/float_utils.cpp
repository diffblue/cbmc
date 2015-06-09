/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <algorithm>

#include <util/arith_tools.h>

#include "float_utils.h"

/*******************************************************************\

Function: float_utilst::set_rounding_mode

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void float_utilst::set_rounding_mode(const bvt &src)
{
  bvt round_to_even=bv_utils.build_constant(ieee_floatt::ROUND_TO_EVEN, src.size());
  bvt round_to_plus_inf=bv_utils.build_constant(ieee_floatt::ROUND_TO_PLUS_INF, src.size());
  bvt round_to_minus_inf=bv_utils.build_constant(ieee_floatt::ROUND_TO_MINUS_INF, src.size());
  bvt round_to_zero=bv_utils.build_constant(ieee_floatt::ROUND_TO_ZERO, src.size());

  rounding_mode_bits.round_to_even=bv_utils.equal(src, round_to_even);
  rounding_mode_bits.round_to_plus_inf=bv_utils.equal(src, round_to_plus_inf);
  rounding_mode_bits.round_to_minus_inf=bv_utils.equal(src, round_to_minus_inf);
  rounding_mode_bits.round_to_zero=bv_utils.equal(src, round_to_zero);
}

/*******************************************************************\

Function: float_utilst::from_signed_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::from_signed_integer(const bvt &src)
{
  unbiased_floatt result;

  // we need to convert negative integers
  result.sign=sign_bit(src);

  result.fraction=bv_utils.absolute_value(src);

  // build an exponent (unbiased) -- this is signed!
  result.exponent=
    bv_utils.build_constant(
      src.size()-1,
      address_bits(src.size()-1).to_long()+1);

  return rounder(result);
}

/*******************************************************************\

Function: float_utilst::from_unsigned_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::from_unsigned_integer(const bvt &src)
{
  unbiased_floatt result;

  result.fraction=src;

  // build an exponent (unbiased) -- this is signed!
  result.exponent=
    bv_utils.build_constant(
      src.size()-1,
      address_bits(src.size()-1).to_long()+1);

  result.sign=const_literal(false);

  return rounder(result);
}

/*******************************************************************\

Function: float_utilst::to_signed_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::to_signed_integer(const bvt &src, unsigned dest_width)
{
  return to_integer(src, dest_width, true);
}

/*******************************************************************\

Function: float_utilst::to_unsigned_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::to_unsigned_integer(const bvt &src, unsigned dest_width)
{
  return to_integer(src, dest_width, false);
}

/*******************************************************************\

Function: float_utilst::to_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::to_integer(
  const bvt &src,
  unsigned dest_width,
  bool is_signed)
{
  assert(src.size()==spec.width());

  const unbiased_floatt unpacked=unpack(src);

  // The following is the usual case in ANSI-C, and we optimize for that.
  if(rounding_mode_bits.round_to_zero.is_true())
  {
    // if the exponent is positive, shift right
    bvt offset=bv_utils.build_constant(spec.f, unpacked.exponent.size());
    bvt distance=bv_utils.sub(offset, unpacked.exponent);
    bvt shift_result=bv_utils.shift(unpacked.fraction, bv_utilst::LRIGHT, distance);

    // if the exponent is negative, we have zero anyways
    bvt result=shift_result;
    literalt exponent_sign=unpacked.exponent[unpacked.exponent.size()-1];

    for(unsigned i=0; i<result.size(); i++)
      result[i]=prop.land(result[i],
                          prop.lnot(exponent_sign));

    // chop out the right number of bits from the result
    if(result.size()>dest_width)
    {
      result.resize(dest_width);
    }
    else if(result.size()<dest_width)
    {
      // zero extend
      result=bv_utils.zero_extension(result, dest_width);
    }

    assert(result.size()==dest_width);

    // if signed, apply sign.
    if(is_signed)
      result=bv_utils.cond_negate(result, unpacked.sign);
    else
    {
      // It's unclear what the behaviour for negative floats
      // to integer shall be.
    }

    return result;
  }
  else
    assert(0);
}

/*******************************************************************\

Function: float_utilst::build_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::build_constant(const ieee_floatt &src)
{
  unbiased_floatt result;

  result.sign=const_literal(src.get_sign());
  result.NaN=const_literal(src.is_NaN());
  result.infinity=const_literal(src.is_infinity());
  result.exponent=bv_utils.build_constant(src.get_exponent(), spec.e);
  result.fraction=bv_utils.build_constant(src.get_fraction(), spec.f+1);

  return pack(bias(result));
}

/*******************************************************************\

Function: float_utilst::conversion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::conversion(
  const bvt &src,
  const ieee_float_spect &dest_spec)
{
  assert(src.size()==spec.width());

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
}

/*******************************************************************\

Function: float_utilst::is_normal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt float_utilst::is_normal(const bvt &src)
{
  return prop.land(
           prop.lnot(exponent_all_zeros(src)),
           prop.lnot(exponent_all_ones(src)));
}

/*******************************************************************\

Function: float_utilst::subtract_exponents

  Inputs:

 Outputs:

 Purpose: Subtracts the exponents

\*******************************************************************/

bvt float_utilst::subtract_exponents(
  const unbiased_floatt &src1,
  const unbiased_floatt &src2)
{
  // extend both
  bvt extended_exponent1=bv_utils.sign_extension(src1.exponent, src1.exponent.size()+1);
  bvt extended_exponent2=bv_utils.sign_extension(src2.exponent, src2.exponent.size()+1);

  assert(extended_exponent1.size()==extended_exponent2.size());

  // compute shift distance (here is the subtraction)
  return bv_utils.sub(extended_exponent1, extended_exponent2);
}

/*******************************************************************\

Function: float_utilst::add_sub

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::add_sub(
  const bvt &src1,
  const bvt &src2,
  bool subtract)
{
  unbiased_floatt unpacked1=unpack(src1);
  unbiased_floatt unpacked2=unpack(src2);

  // subtract?
  if(subtract)
    unpacked2.sign=prop.lnot(unpacked2.sign);

  // figure out which operand has the bigger exponent
  const bvt exponent_difference=subtract_exponents(unpacked1, unpacked2);
  literalt src2_bigger=exponent_difference.back();

  const bvt bigger_exponent=
    bv_utils.select(src2_bigger, unpacked2.exponent, unpacked1.exponent);

  // swap fractions as needed
  const bvt new_fraction1=
    bv_utils.select(src2_bigger, unpacked2.fraction, unpacked1.fraction);

  const bvt new_fraction2=
    bv_utils.select(src2_bigger, unpacked1.fraction, unpacked2.fraction);

  // compute distance
  const bvt distance=bv_utils.absolute_value(exponent_difference);

  // limit the distance: shifting more than f+3 bits is unnecessary
  const bvt limited_dist=limit_distance(distance, spec.f+3);

  // pad fractions with 2 zeros from below
  const bvt fraction1_padded=bv_utils.concatenate(bv_utils.zeros(3), new_fraction1);
  const bvt fraction2_padded=bv_utils.concatenate(bv_utils.zeros(3), new_fraction2);

  // shift new_fraction2
  literalt sticky_bit;
  const bvt fraction1_shifted=fraction1_padded;
  const bvt fraction2_shifted=sticky_right_shift(
    fraction2_padded, limited_dist, sticky_bit);

  // sticky bit: or of the bits lost by the right-shift
  bvt fraction2_stickied=fraction2_shifted;
  fraction2_stickied[0]=prop.lor(fraction2_shifted[0], sticky_bit);

  // need to have two extra fraction bits for addition and rounding
  const bvt fraction1_ext=bv_utils.zero_extension(fraction1_shifted, fraction1_shifted.size()+2);
  const bvt fraction2_ext=bv_utils.zero_extension(fraction2_stickied, fraction2_stickied.size()+2);

  unbiased_floatt result;

  // now add/sub them
  literalt subtract_lit=prop.lxor(unpacked1.sign, unpacked2.sign);
  result.fraction=
    bv_utils.add_sub(fraction1_ext, fraction2_ext, subtract_lit);

  // sign of result
  literalt fraction_sign=result.fraction.back();
  result.fraction=bv_utils.absolute_value(result.fraction);

  result.exponent=bigger_exponent;

  // adjust the exponent for the fact that we added two bits to the fraction
  result.exponent=
    bv_utils.add(bv_utils.sign_extension(result.exponent, result.exponent.size()+1),
      bv_utils.build_constant(2, result.exponent.size()+1));

  // NaN?
  result.NaN=prop.lor(
      prop.land(prop.land(unpacked1.infinity, unpacked2.infinity),
                prop.lxor(unpacked1.sign, unpacked2.sign)),
      prop.lor(unpacked1.NaN, unpacked2.NaN));

  // infinity?
  result.infinity=prop.land(
      prop.lnot(result.NaN),
      prop.lor(unpacked1.infinity, unpacked2.infinity));

  // zero?
  // Note that:
  //  1. The zero flag isn't used apart from in divide and
  //     is only set on unpack
  //  2. Subnormals mean that addition or subtraction can't round to 0,
  //     thus we can perform this test now
  //  3. The rules for sign are different for zero
  result.zero = prop.land(
      prop.lnot(prop.lor(result.infinity, result.NaN)),
      prop.lnot(prop.lor(result.fraction)));


  // sign
  literalt add_sub_sign=
    prop.lxor(prop.lselect(src2_bigger, unpacked2.sign, unpacked1.sign),
              fraction_sign);

  literalt infinity_sign=
    prop.lselect(unpacked1.infinity, unpacked1.sign, unpacked2.sign);

  #if 1
  literalt zero_sign=
    prop.lselect(rounding_mode_bits.round_to_minus_inf,
                 prop.lor(unpacked1.sign, unpacked2.sign),
                 prop.land(unpacked1.sign, unpacked2.sign));

  result.sign=prop.lselect( 
    result.infinity,
    infinity_sign,
    prop.lselect(result.zero,
                 zero_sign,
                 add_sub_sign));
  #else
  result.sign=prop.lselect(
    result.infinity,
    infinity_sign,
    add_sub_sign);
  #endif

  #if 0
  result.sign=const_literal(false);
  result.fraction.resize(spec.f+1, const_literal(true));
  result.exponent.resize(spec.e, const_literal(false));
  result.NaN=const_literal(false);
  result.infinity=const_literal(false);
  //for(unsigned i=0; i<result.fraction.size(); i++)
  //  result.fraction[i]=const_literal(true);

  for(unsigned i=0; i<result.fraction.size(); i++)
    result.fraction[i]=new_fraction2[i];

  return pack(bias(result));
  #endif

  return rounder(result);
}

/*******************************************************************\

Function: float_utilst::limit_distance

  Inputs:

 Outputs:

 Purpose: Limits the shift distance

\*******************************************************************/

bvt float_utilst::limit_distance(
    const bvt &dist,
    mp_integer limit)
{
  unsigned nb_bits=integer2unsigned(address_bits(limit));

  bvt upper_bits=dist;
  upper_bits.erase(upper_bits.begin(), upper_bits.begin()+nb_bits);
  literalt or_upper_bits=prop.lor(upper_bits);

  bvt lower_bits=dist;
  lower_bits.resize(nb_bits);

  bvt result;
  result.resize(lower_bits.size());

  // bitwise or with or_upper_bits
  for(unsigned int i=0; i<result.size(); i++)
    result[i]=prop.lor(lower_bits[i], or_upper_bits);

  return result;
}

/*******************************************************************\

Function: float_utilst::mul

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::mul(const bvt &src1, const bvt &src2)
{
  // unpack
  const unbiased_floatt unpacked1=unpack(src1);
  const unbiased_floatt unpacked2=unpack(src2);

  // zero-extend the fractions
  const bvt fraction1=bv_utils.zero_extension(unpacked1.fraction, unpacked1.fraction.size()*2);
  const bvt fraction2=bv_utils.zero_extension(unpacked2.fraction, unpacked2.fraction.size()*2);

  // multiply fractions
  unbiased_floatt result;
  result.fraction=bv_utils.unsigned_multiplier(fraction1, fraction2);

  // extend exponents to account for overflow
  // add two bits, as we do extra arithmetic on it later
  const bvt exponent1=bv_utils.sign_extension(unpacked1.exponent, unpacked1.exponent.size()+2);
  const bvt exponent2=bv_utils.sign_extension(unpacked2.exponent, unpacked2.exponent.size()+2);

  bvt added_exponent=bv_utils.add(exponent1, exponent2);

  // adjust, we are thowing in an extra fraction bit
  // it has been extended above
  result.exponent=bv_utils.inc(added_exponent);

  // new sign
  result.sign=prop.lxor(unpacked1.sign, unpacked2.sign);

  // infinity?
  result.infinity=prop.lor(unpacked1.infinity, unpacked2.infinity);

  // NaN?
  {
    bvt NaN_cond;

    NaN_cond.push_back(is_NaN(src1));
    NaN_cond.push_back(is_NaN(src2));

    // infinity * 0 is NaN!
    NaN_cond.push_back(prop.land(unpacked1.zero, unpacked2.infinity));
    NaN_cond.push_back(prop.land(unpacked2.zero, unpacked1.infinity));

    result.NaN=prop.lor(NaN_cond);
  }

  return rounder(result);
}

/*******************************************************************\

Function: float_utilst::div

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::div(const bvt &src1, const bvt &src2)
{
  // unpack
  const unbiased_floatt unpacked1=unpack(src1);
  const unbiased_floatt unpacked2=unpack(src2);
  
  unsigned div_width=unpacked1.fraction.size()*2+1;

  // pad fraction1 with zeros
  bvt fraction1=unpacked1.fraction;
  fraction1.reserve(div_width);
  while(fraction1.size()<div_width)
    fraction1.insert(fraction1.begin(), const_literal(false));

  // zero-extend fraction2
  const bvt fraction2=
    bv_utils.zero_extension(unpacked2.fraction, div_width);

  // divide fractions
  unbiased_floatt result;
  bvt rem;
  bv_utils.unsigned_divider(fraction1, fraction2, result.fraction, rem);
  
  // is there a remainder?
  literalt have_remainder=bv_utils.is_not_zero(rem);
  
  // we throw this into the result, as one additional bit,
  // to get the right rounding decision
  result.fraction.insert(
    result.fraction.begin(), have_remainder);
    
  // We will subtract the exponents;
  // to account for overflow, we add a bit.
  const bvt exponent1=bv_utils.sign_extension(unpacked1.exponent, unpacked1.exponent.size()+1);
  const bvt exponent2=bv_utils.sign_extension(unpacked2.exponent, unpacked2.exponent.size()+1);

  // subtract exponents
  bvt added_exponent=bv_utils.sub(exponent1, exponent2);

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
    prop.lor(
      prop.land(prop.lnot(unpacked1.zero),
      prop.land(prop.lnot(unpacked1.NaN),
                unpacked2.zero)),
      prop.land(unpacked1.infinity,
      prop.land(prop.lnot(unpacked2.NaN),
                prop.lnot(unpacked2.zero))));

  // NaN?
  result.NaN=prop.lor(unpacked1.NaN,
             prop.lor(unpacked2.NaN,
             prop.lor(prop.land(unpacked1.zero, unpacked2.zero),
                      prop.land(unpacked1.infinity, unpacked2.infinity))));

  // Division by infinity produces zero, unless we have NaN
  literalt force_zero=
    prop.land(prop.lnot(unpacked1.NaN), unpacked2.infinity);
  
  result.fraction=bv_utils.select(force_zero,
    bv_utils.zeros(result.fraction.size()), result.fraction);

  return rounder(result);
}

/*******************************************************************\

Function: float_utilst::rem

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::rem(const bvt &src1, const bvt &src2)
{
  /* The semantics of floating-point remainder implemented as below
     is the sensible one.  Unfortunately this is not the one required
     by IEEE-754 or fmod / remainder.  Martin has discussed the
     'correct' semantics with Christoph and Alberto at length as
     well as talking to various hardware designers and we still
     hasn't found a good way to implement them in a solver.
     We have some approaches that are correct but they really
     don't scale. */

  // stub: do src1-(src1/src2)*src2
  return sub(src1, mul(div(src1, src2), src2));
}

/*******************************************************************\

Function: float_utilst::negate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::negate(const bvt &src)
{
  bvt result=src;
  assert(!src.empty());
  literalt &sign_bit=result[result.size()-1];
  sign_bit=prop.lnot(sign_bit);
  return result;
}

/*******************************************************************\

Function: float_utilst::abs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::abs(const bvt &src)
{
  bvt result=src;
  assert(!src.empty());
  result[result.size()-1]=const_literal(false);
  return result;
}

/*******************************************************************\

Function: float_utilst::relation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt float_utilst::relation(
  const bvt &src1,
  relt rel,
  const bvt &src2)
{
  if(rel==GT)
    return relation(src2, LT, src1); // swapped
  else if(rel==GE)
    return relation(src2, LE, src1); // swapped

  assert(rel==EQ || rel==LT || rel==LE);

  // special cases: -0 and 0 are equal
  literalt is_zero1=is_zero(src1);
  literalt is_zero2=is_zero(src2);
  literalt both_zero=prop.land(is_zero1, is_zero2);

  // NaN compares to nothing
  literalt is_NaN1=is_NaN(src1);
  literalt is_NaN2=is_NaN(src2);
  literalt NaN=prop.lor(is_NaN1, is_NaN2);

  if(rel==LT || rel==LE)
  {
    literalt bitwise_equal=bv_utils.equal(src1, src2);

    // signs different? trivial! Unless Zero.

    literalt signs_different=
      prop.lxor(sign_bit(src1), sign_bit(src2));

    // as long as the signs match: compare like unsigned numbers

    // this works due to the BIAS
    literalt less_than1=bv_utils.unsigned_less_than(src1, src2);

    // if both are negative (and not the same), need to turn around!
    literalt less_than2=
        prop.lxor(less_than1, prop.land(sign_bit(src1), sign_bit(src2)));

    literalt less_than3=
      prop.lselect(signs_different,
        sign_bit(src1),
        less_than2);

    if(rel==LT)
    {
      bvt and_bv;
      and_bv.push_back(less_than3);
      and_bv.push_back(prop.lnot(bitwise_equal)); // for the case of two negative numbers
      and_bv.push_back(prop.lnot(both_zero));
      and_bv.push_back(prop.lnot(NaN));

      return prop.land(and_bv);
    }
    else if(rel==LE)
    {
      bvt or_bv;
      or_bv.push_back(less_than3);
      or_bv.push_back(both_zero);
      or_bv.push_back(bitwise_equal);

      return prop.land(prop.lor(or_bv), prop.lnot(NaN));
    }
    else
      assert(false);
  }
  else if(rel==EQ)
  {
    literalt bitwise_equal=bv_utils.equal(src1, src2);

    return prop.land(
      prop.lor(bitwise_equal, both_zero),
      prop.lnot(NaN));
  }
  else
    assert(0);
    
  // not reached
  return const_literal(false);
}

/*******************************************************************\

Function: float_utilst::is_zero

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt float_utilst::is_zero(const bvt &src)
{
  assert(!src.empty());
  bvt all_but_sign;
  all_but_sign=src;
  all_but_sign.resize(all_but_sign.size()-1);
  return bv_utils.is_zero(all_but_sign);
}

/*******************************************************************\

Function: float_utilst::is_plus_inf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt float_utilst::is_plus_inf(const bvt &src)
{
  bvt and_bv;
  and_bv.push_back(prop.lnot(sign_bit(src)));
  and_bv.push_back(exponent_all_ones(src));
  and_bv.push_back(fraction_all_zeros(src));
  return prop.land(and_bv);
}

/*******************************************************************\

Function: float_utilst::infinity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt float_utilst::is_infinity(const bvt &src)
{
  return prop.land(
    exponent_all_ones(src),
    fraction_all_zeros(src));
}

/*******************************************************************\

Function: float_utilst::get_exponent

  Inputs:

 Outputs:

 Purpose: Gets the unbiased exponent in a floating-point bit-vector

\*******************************************************************/

bvt float_utilst::get_exponent(const bvt &src)
{
  return bv_utils.extract(src, spec.f, spec.f+spec.e-1);
}

/*******************************************************************\

Function: float_utilst::get_fraction

  Inputs:

 Outputs:

 Purpose: Gets the fraction without hidden bit in a floating-point
          bit-vector src

\*******************************************************************/

bvt float_utilst::get_fraction(const bvt &src)
{
  return bv_utils.extract(src, 0, spec.f-1);
}

/*******************************************************************\

Function: float_utilst::is_minus_inf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt float_utilst::is_minus_inf(const bvt &src)
{
  bvt and_bv;
  and_bv.push_back(sign_bit(src));
  and_bv.push_back(exponent_all_ones(src));
  and_bv.push_back(fraction_all_zeros(src));
  return prop.land(and_bv);
}

/*******************************************************************\

Function: float_utilst::is_NaN

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt float_utilst::is_NaN(const bvt &src)
{
  return prop.land(exponent_all_ones(src),
                   prop.lnot(fraction_all_zeros(src)));
}

/*******************************************************************\

Function: float_utilst::exponent_all_ones

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt float_utilst::exponent_all_ones(const bvt &src)
{
  bvt exponent=src;

  // removes the fractional part
  exponent.erase(exponent.begin(), exponent.begin()+spec.f);

  // removes the sign
  exponent.resize(spec.e);

  return bv_utils.is_all_ones(exponent);
}

/*******************************************************************\

Function: float_utilst::exponent_all_zeros

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt float_utilst::exponent_all_zeros(const bvt &src)
{
  bvt exponent=src;

  // removes the fractional part
  exponent.erase(exponent.begin(), exponent.begin()+spec.f);

  // removes the sign
  exponent.resize(spec.e);

  return bv_utils.is_zero(exponent);
}

/*******************************************************************\

Function: float_utilst::fraction_all_zeros

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt float_utilst::fraction_all_zeros(const bvt &src)
{
  // does not include hidden bit
  bvt tmp=src;
  assert(src.size()==spec.width());
  tmp.resize(spec.f);
  return bv_utils.is_zero(tmp);
}

/*******************************************************************\

Function: float_utilst::normalization_shift

  Inputs:

 Outputs:

 Purpose: normalize fraction/exponent pair
          returns 'zero' if fraction is zero

\*******************************************************************/

void float_utilst::normalization_shift(bvt &fraction, bvt &exponent)
{
  #if 0
  // this thing is quadratic!

  bvt new_fraction=prop.new_variables(fraction.size());
  bvt new_exponent=prop.new_variables(exponent.size());

  // i is the shift distance
  for(unsigned i=0; i<fraction.size(); i++)
  {
    bvt equal;

    // the bits above need to be zero
    for(unsigned j=0; j<i; j++)
      equal.push_back(
        prop.lnot(fraction[fraction.size()-1-j]));

    // this one needs to be one
    equal.push_back(fraction[fraction.size()-1-i]);

    // iff all of that holds, we shift here!
    literalt shift=prop.land(equal);

    // build shifted value
    bvt shifted_fraction=bv_utils.shift(fraction, bv_utilst::LEFT, i);
    bv_utils.cond_implies_equal(shift, shifted_fraction, new_fraction);

    // build new exponent
    bvt adjustment=bv_utils.build_constant(-i, exponent.size());
    bvt added_exponent=bv_utils.add(exponent, adjustment);
    bv_utils.cond_implies_equal(shift, added_exponent, new_exponent);
  }

  // Fraction all zero? It stays zero.
  // The exponent is undefined in that case.
  literalt fraction_all_zero=bv_utils.is_zero(fraction);
  bvt zero_fraction;
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
  
  bvt exponent_delta=bv_utils.zeros(exponent.size());
  
  for(int d=depth-1; d>=0; d--)
  {
    unsigned distance=(1<<d);
    assert(fraction.size()>distance);
    
    // check if first 'distance'-many bits are zeros
    const bvt prefix=bv_utils.extract_msb(fraction, distance);
    literalt prefix_is_zero=bv_utils.is_zero(prefix);
    
    // If so, shift the zeros out left by 'distance'.
    // Otherwise, leave as is.
    const bvt shifted=
      bv_utils.shift(fraction, bv_utilst::LEFT, distance);
    
    fraction=
      bv_utils.select(prefix_is_zero, shifted, fraction);
      
    // add corresponding weight to exponent
    assert(d<(signed)exponent_delta.size());
    exponent_delta[d]=prefix_is_zero;
  }  
    
  exponent=bv_utils.sub(exponent, exponent_delta);
  
  #endif
}

/*******************************************************************\

Function: float_utilst::denormalization_shift

  Inputs:

 Outputs:

 Purpose: make sure exponent is not too small;
          the exponent is unbiased

\*******************************************************************/

void float_utilst::denormalization_shift(bvt &fraction, bvt &exponent)
{
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

  bvt distance=bv_utils.sub(
    bv_utils.build_constant(-bias+1, exponent.size()), exponent);

  // use sign bit
  literalt denormal=prop.land(
    prop.lnot(distance.back()),
    prop.lnot(bv_utils.is_zero(distance)));

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

  bvt denormalisedFraction = fraction;

  literalt sticky_bit = const_literal(false);
  denormalisedFraction = 
    sticky_right_shift(fraction, distance, sticky_bit);
  denormalisedFraction[0] = prop.lor(denormalisedFraction[0], sticky_bit);

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
}

/*******************************************************************\

Function: float_utilst::rounder

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::rounder(const unbiased_floatt &src)
{
  // incoming: some fraction (with explicit 1),
  //           some exponent without bias
  // outgoing: rounded, with right size, with hidden bit, bias

  bvt aligned_fraction=src.fraction,
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
}

/*******************************************************************\

Function: float_utilst::fraction_rounding_decision

  Inputs:

 Outputs:

 Purpose: rounding decision for fraction using sticky bit

\*******************************************************************/

literalt float_utilst::fraction_rounding_decision(
  const unsigned dest_bits,
  const literalt sign,
  const bvt &fraction)
{
  assert(dest_bits<fraction.size());

  // we have too many fraction bits
  unsigned extra_bits=fraction.size()-dest_bits;

  // more than two extra bits are superflus, and are
  // turned into a sticky bit

  literalt sticky_bit=const_literal(false);

  if(extra_bits>=2)
  {
    // We keep most-significant bits, and thus the tail is made
    // of least-significant bits.
    bvt tail=bv_utils.extract(fraction, 0, extra_bits-2);
    sticky_bit=prop.lor(tail);
  }

  // the rounding bit is the last extra bit
  assert(extra_bits>=1);
  literalt rounding_bit=fraction[extra_bits-1];

  // we get one bit of the fraction for some rounding decisions
  literalt rounding_least=fraction[extra_bits];

  // round-to-nearest (ties to even)
  literalt round_to_even=
    prop.land(rounding_bit,
              prop.lor(rounding_least, sticky_bit));
  
  // round up
  literalt round_to_plus_inf=
    prop.land(prop.lnot(sign),
              prop.lor(rounding_bit, sticky_bit));

  // round down
  literalt round_to_minus_inf=
    prop.land(sign,
              prop.lor(rounding_bit, sticky_bit));

  // round to zero
  literalt round_to_zero=
    const_literal(false);

  // now select appropriate one
  return prop.lselect(rounding_mode_bits.round_to_even, round_to_even,
         prop.lselect(rounding_mode_bits.round_to_plus_inf, round_to_plus_inf,
         prop.lselect(rounding_mode_bits.round_to_minus_inf, round_to_minus_inf,
         prop.lselect(rounding_mode_bits.round_to_zero, round_to_zero,
           prop.new_variable())))); // otherwise non-det
}                

/*******************************************************************\

Function: float_utilst::round_fraction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void float_utilst::round_fraction(unbiased_floatt &result)
{
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
    literalt increment=fraction_rounding_decision(
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

    literalt overflow=result.fraction.back();

    // In case of an overflow, the exponent has to be incremented.
    // "Post normalization" is then required.
    result.exponent=
      bv_utils.incrementer(result.exponent, overflow);

    // post normalization of the fraction
    literalt integer_part1=result.fraction.back();
    literalt integer_part0=result.fraction[result.fraction.size()-2];
    literalt new_integer_part=prop.lor(integer_part1, integer_part0);

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
    literalt oldMSB = result.fraction.back();

    result.fraction=bv_utils.incrementer(result.fraction, increment);

    // Normal overflow when old MSB == 1 and new MSB == 0
    literalt overflow=prop.land(oldMSB, neg(result.fraction.back()));

    // Subnormal to normal transition when old MSB == 0 and new MSB == 1
    literalt subnormal_to_normal=
      prop.land(neg(oldMSB), result.fraction.back());

    // In case of an overflow or subnormal to normal conversion,
    // the exponent has to be incremented.
    result.exponent=
      bv_utils.incrementer(result.exponent, 
                           prop.lor(overflow, subnormal_to_normal));

    // post normalization of the fraction
    // In the case of overflow, set the MSB to 1
    // The subnormal case will have (only) the MSB set to 1
    result.fraction.back() = prop.lor(result.fraction.back(), overflow);
#endif

  }
}

/*******************************************************************\

Function: float_utilst::round_exponent

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void float_utilst::round_exponent(unbiased_floatt &result)
{
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
    bvt old_exponent=result.exponent;
    result.exponent.resize(spec.e);

    // max_exponent is the maximum representable
    // i.e. 1 higher than the maximum possible for a normal number
    bvt max_exponent=
      bv_utils.build_constant(
        spec.max_exponent()-spec.bias(), old_exponent.size());

    // the exponent is garbage if the fractional is zero

    literalt exponent_too_large=
      prop.land(
        prop.lnot(
          bv_utils.signed_less_than(old_exponent, max_exponent)),
        prop.lnot(bv_utils.is_zero(result.fraction)));

#if 1
    // Directed rounding modes round overflow to the maximum normal
    // depending on the particular mode and the sign
    literalt overflow_to_inf=
      prop.lor(rounding_mode_bits.round_to_even,
      prop.lor(prop.land(rounding_mode_bits.round_to_plus_inf,
                         prop.lnot(result.sign)),
               prop.land(rounding_mode_bits.round_to_minus_inf,
                         result.sign)));

    literalt set_to_max=
      prop.land(exponent_too_large, prop.lnot(overflow_to_inf));


    bvt largest_normal_exponent=
      bv_utils.build_constant(
        spec.max_exponent()-(spec.bias() + 1), result.exponent.size());

    result.exponent=
      bv_utils.select(set_to_max, largest_normal_exponent, result.exponent);

    result.fraction=
      bv_utils.select(set_to_max,
                      bv_utils.inverted(bv_utils.zeros(result.fraction.size())),
                      result.fraction);

    result.infinity=prop.lor(result.infinity, 
                             prop.land(exponent_too_large,
                                       overflow_to_inf));
#else
    result.infinity=prop.lor(result.infinity, exponent_too_large);
#endif
  }
}

/*******************************************************************\

Function: float_utilst::bias

  Inputs:

 Outputs:

 Purpose: takes an unbiased float, and applies the bias

\*******************************************************************/

float_utilst::biased_floatt float_utilst::bias(const unbiased_floatt &src)
{
  biased_floatt result;

  result.sign=src.sign;
  result.NaN=src.NaN;
  result.infinity=src.infinity;

  // we need to bias the new exponent
  result.exponent=add_bias(src.exponent);

  // strip off hidden bit
  assert(src.fraction.size()==spec.f+1);

  literalt hidden_bit=src.fraction[src.fraction.size()-1];
  literalt denormal=prop.lnot(hidden_bit);

  result.fraction=src.fraction;
  result.fraction.resize(spec.f);

  // make exponent zero if its denormal
  // (includes zero)
  for(unsigned i=0; i<result.exponent.size(); i++)
    result.exponent[i]=
      prop.land(result.exponent[i], prop.lnot(denormal));

  return result;
}

/*******************************************************************\

Function: float_utilst::add_bias

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::add_bias(const bvt &src)
{
  assert(src.size()==spec.e);

  return bv_utils.add(
    src,
    bv_utils.build_constant(spec.bias(), spec.e));
}

/*******************************************************************\

Function: float_utilst::sub_bias

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::sub_bias(const bvt &src)
{
  assert(src.size()==spec.e);

  return bv_utils.sub(
    src,
    bv_utils.build_constant(spec.bias(), spec.e));
}

/*******************************************************************\

Function: float_utilst::unpack

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

float_utilst::unbiased_floatt float_utilst::unpack(const bvt &src)
{
  assert(src.size()==spec.width());

  unbiased_floatt result;

  result.sign=sign_bit(src);

  result.fraction=get_fraction(src);
  result.fraction.push_back(is_normal(src)); // add hidden bit

  result.exponent=get_exponent(src);
  assert(result.exponent.size()==spec.e);

  // unbias the exponent
  literalt denormal=bv_utils.is_zero(result.exponent);

  result.exponent=
    bv_utils.select(denormal,
      bv_utils.build_constant(-spec.bias()+1, spec.e),
      sub_bias(result.exponent));

  result.infinity=is_infinity(src);
  result.zero=is_zero(src);
  result.NaN=is_NaN(src);

  return result;
}

/*******************************************************************\

Function: float_utilst::pack

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::pack(const biased_floatt &src)
{
  assert(src.fraction.size()==spec.f);
  assert(src.exponent.size()==spec.e);

  bvt result;
  result.resize(spec.width());

  // do sign
  // we make this 'false' for NaN
  result[result.size()-1]=
    prop.lselect(src.NaN, const_literal(false), src.sign);

  literalt infinity_or_NaN=
    prop.lor(src.NaN, src.infinity);

  // just copy fraction
  for(unsigned i=0; i<spec.f; i++)
    result[i]=prop.land(src.fraction[i], prop.lnot(infinity_or_NaN));

  result[0]=prop.lor(result[0], src.NaN);

  // do exponent
  for(unsigned i=0; i<spec.e; i++)
    result[i+spec.f]=prop.lor(
      src.exponent[i],
      infinity_or_NaN);

  return result;
}

/*******************************************************************\

Function: float_utilst::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ieee_floatt float_utilst::get(const bvt &src) const
{
  mp_integer int_value=0;

  for(unsigned i=0; i<src.size(); i++)
    int_value+=power(2, i)*prop.l_get(src[i]).is_true();

  ieee_floatt result;
  result.spec=spec;
  result.unpack(int_value);

  return result;
}

/*******************************************************************\

Function: float_utilst::sticky_right_shift

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::sticky_right_shift(
  const bvt &op,
  const bvt &dist,
  literalt &sticky)
{
  unsigned d=1;
  bvt result=op;
  sticky=const_literal(false);

  for(unsigned stage=0; stage<dist.size(); stage++)
  {
    if(dist[stage]!=const_literal(false))
    {
      bvt tmp=bv_utils.shift(result, bv_utilst::LRIGHT, d);

      bvt lost_bits;

      if(d<=result.size())
        lost_bits=bv_utils.extract(result, 0, d-1);
      else
        lost_bits=result;

      sticky=prop.lor(
          prop.land(dist[stage],prop.lor(lost_bits)),
          sticky);

      result=bv_utils.select(dist[stage], tmp, result);
    }

    d=d<<1;
  }

  return result;
}

/*******************************************************************\

Function: float_utilst::debug1

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::debug1(
  const bvt &src1,
  const bvt &src2)
{
  return src1;
}

/*******************************************************************\

Function: float_utilst::debug1

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bvt float_utilst::debug2(
  const bvt &op0,
  const bvt &op1)
{
  return op0;
}

