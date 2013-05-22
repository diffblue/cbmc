/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FLOAT_UTILS_H
#define CPROVER_FLOAT_UTILS_H

#include <util/ieee_float.h>

#include <solvers/flattening/bv_utils.h>

class float_utilst
{
public:
  ieee_floatt::rounding_modet rounding_mode;

  struct rounding_mode_bitst
  {
  public:
    // these are mutually exclusive, obviously
    literalt round_to_even;
    literalt round_to_zero;
    literalt round_to_plus_inf;
    literalt round_to_minus_inf;

    rounding_mode_bitst():
      round_to_even(const_literal(true)),
      round_to_zero(const_literal(false)),
      round_to_plus_inf(const_literal(false)),
      round_to_minus_inf(const_literal(false))
    {
    }
  };

  explicit float_utilst(propt &_prop):
    rounding_mode(ieee_floatt::ROUND_TO_EVEN),
    prop(_prop),
    bv_utils(_prop)
  {
  }

  virtual ~float_utilst()
  {
  }

  ieee_float_spect spec;

  bvt build_constant(const ieee_floatt &src);

  static inline literalt sign_bit(const bvt &src)
  {
    // this is the top bit
    return src[src.size()-1];
  }

  // extraction
  bvt get_exponent(const bvt &src); // still biased
  bvt get_fraction(const bvt &src); // without hidden bit
  literalt is_normal(const bvt &src);
  literalt is_zero(const bvt &src); // this returns true on both 0 and -0
  literalt is_infinity(const bvt &src);
  literalt is_plus_inf(const bvt &src);
  literalt is_minus_inf(const bvt &src);
  literalt is_NaN(const bvt &src);

  // add/sub
  virtual bvt add_sub(const bvt &src1, const bvt &src2, bool subtract);
  bvt add(const bvt &src1, const bvt &src2) { return add_sub(src1, src2, false); }
  bvt sub(const bvt &src1, const bvt &src2) { return add_sub(src1, src2, true); }

  // mul/div
  virtual bvt mul(const bvt &src1, const bvt &src2);
  virtual bvt div(const bvt &src1, const bvt &src2);

  bvt abs(const bvt &src);
  bvt inverse(const bvt &src);
  bvt negate(const bvt &src);

  // conversion
  bvt from_unsigned_integer(const bvt &src);
  bvt from_signed_integer(const bvt &src);
  bvt to_integer(const bvt &src, unsigned int_width, bool is_signed);
  bvt to_signed_integer(const bvt &src, unsigned int_width);
  bvt to_unsigned_integer(const bvt &src, unsigned int_width);
  bvt conversion(const bvt &src, const ieee_float_spect &dest_spec);

  // relations
  typedef enum { LT, LE, EQ, GT, GE } relt;
  literalt relation(const bvt &src1, relt rel, const bvt &src2);

  // constants
  ieee_floatt get(const bvt &src) const;

  // helpers
  literalt exponent_all_ones(const bvt &src);
  literalt exponent_all_zeros(const bvt &src);
  literalt fraction_all_zeros(const bvt &src);
    
  // debugging hooks
  bvt debug1(const bvt &op0, const bvt &op1);
  bvt debug2(const bvt &op0, const bvt &op1);

protected:
  propt &prop;
  bv_utilst bv_utils;

  // unpacked
  virtual void normalization_shift(bvt &fraction, bvt &exponent);
  void denormalization_shift(bvt &fraction, bvt &exponent);

  bvt add_bias(const bvt &exponent);
  bvt sub_bias(const bvt &exponent);

  bvt limit_distance(const bvt &dist, mp_integer limit);

  struct unpacked_floatt
  {
    literalt sign;
    literalt infinity;
    literalt zero;
    literalt NaN;
    bvt fraction;
    bvt exponent;

    unpacked_floatt():
      sign(const_literal(false)),
      infinity(const_literal(false)),
      zero(const_literal(false)),
      NaN(const_literal(false))
    {
    }
  };

  // this has a biased exponent
  // and an _implicit_ hidden bit
  struct biased_floatt:public unpacked_floatt
  {
  };

  // the hidden bit is explicit,
  // and the exponent is not biased
  struct unbiased_floatt:public unpacked_floatt
  {
  };

  biased_floatt bias(const unbiased_floatt &src);

  // this takes unpacked format, and returns packed
  virtual bvt rounder(const unbiased_floatt &src);
  bvt pack(const biased_floatt &src);
  unbiased_floatt unpack(const bvt &src);

  void round_fraction(unbiased_floatt &result);
  void round_exponent(unbiased_floatt &result);
  
  // rounding decision for fraction
  literalt fraction_rounding_decision(
    const unsigned dest_bits,
    const literalt sign,
    const bvt &fraction);

  // helpers for adder

  // computes src1.exponent-src2.exponent with extension
  bvt subtract_exponents(
    const unbiased_floatt &src1,
    const unbiased_floatt &src2);

  // computes the "sticky-bit"
  bvt sticky_right_shift(
    const bvt &op,
    const bv_utilst::shiftt shift_type,
    const bvt &dist,
    literalt &sticky);
};

#endif
