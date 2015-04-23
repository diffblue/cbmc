/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FLOAT_BV_H
#define CPROVER_FLOAT_BV_H

#include <util/i2string.h>
#include <util/ieee_float.h>
#include <util/std_expr.h>

#include "../flattening/bv_utils.h"

class float_bvt
{
public:
  explicit float_bvt()
  {
  }

  ~float_bvt()
  {
  }

  inline exprt operator()(const exprt &src)
  {
    return convert(src);
  }
  
  exprt convert(const exprt &);

  exprt negation(const exprt &, const ieee_float_spect &);
  exprt abs(const exprt &, const ieee_float_spect &);
  exprt is_equal(const exprt &, const exprt &, const ieee_float_spect &);
  exprt is_zero(const exprt &, const ieee_float_spect &);
  exprt isnan(const exprt &, const ieee_float_spect &);
  exprt isinf(const exprt &, const ieee_float_spect &);
  exprt isnormal(const exprt &, const ieee_float_spect &);
  exprt isfinite(const exprt &, const ieee_float_spect &);

  // add/sub
  exprt add_sub(bool subtract, const exprt &, const exprt &, const exprt &rm, const ieee_float_spect &);
  
  // mul/div
  exprt mul(const exprt &, const exprt &, const exprt &rm, const ieee_float_spect &);
  exprt div(const exprt &, const exprt &, const exprt &rm, const ieee_float_spect &);

  // conversion
  exprt from_unsigned_integer(const exprt &, const exprt &rm, const ieee_float_spect &);
  exprt from_signed_integer(const exprt &, const exprt &rm, const ieee_float_spect &);
  exprt to_signed_integer(const exprt &src, unsigned dest_width, const exprt &rm, const ieee_float_spect &);
  exprt to_unsigned_integer(const exprt &src, unsigned dest_width, const exprt &rm, const ieee_float_spect &);
  exprt to_integer(const exprt &src, unsigned dest_width, bool is_signed, const exprt &rm, const ieee_float_spect &);
  exprt conversion(const exprt &src, const exprt &rm, const ieee_float_spect &src_spec, const ieee_float_spect &dest_spec);

  // relations
  typedef enum { LT, LE, EQ, GT, GE } relt;
  exprt relation(const exprt &, relt rel, const exprt &, const ieee_float_spect &);

protected:
  // helpers
  ieee_float_spect get_spec(const exprt &);
  exprt get_exponent(const exprt &, const ieee_float_spect &); // still biased
  exprt get_fraction(const exprt &, const ieee_float_spect &); // without hidden bit
  exprt sign_bit(const exprt &);

  exprt exponent_all_ones(const exprt &, const ieee_float_spect &);
  exprt exponent_all_zeros(const exprt &, const ieee_float_spect &);
  exprt fraction_all_zeros(const exprt &, const ieee_float_spect &);

  struct rounding_mode_bitst
  {
  public:
    // these are mutually exclusive, obviously
    exprt round_to_even;
    exprt round_to_zero;
    exprt round_to_plus_inf;
    exprt round_to_minus_inf;
    
    void get(const exprt &rm);
    explicit rounding_mode_bitst(const exprt &rm) { get(rm); }
  };

  // unpacked
  void normalization_shift(exprt &fraction, exprt &exponent);
  void denormalization_shift(exprt &fraction, exprt &exponent, const ieee_float_spect &);

  exprt add_bias(const exprt &exponent, const ieee_float_spect &);
  exprt sub_bias(const exprt &exponent, const ieee_float_spect &);

  exprt limit_distance(const exprt &dist, mp_integer limit);

  struct unpacked_floatt
  {
    exprt sign, infinity, zero, NaN;
    exprt fraction, exponent;
    
    unpacked_floatt():
      sign(false_exprt()),
      infinity(false_exprt()),
      zero(false_exprt()),
      NaN(false_exprt())
    {
    }
  };

  // This has a biased exponent (unsigned)
  // and an _implicit_ hidden bit.
  struct biased_floatt:public unpacked_floatt
  {
  };

  // The hidden bit is explicit,
  // and the exponent is not biased (signed)
  struct unbiased_floatt:public unpacked_floatt
  {
  };

  biased_floatt bias(const unbiased_floatt &, const ieee_float_spect &);

  // this takes unpacked format, and returns packed
  virtual exprt rounder(const unbiased_floatt &, const exprt &rm, const ieee_float_spect &);
  exprt pack(const biased_floatt &, const ieee_float_spect &);
  unbiased_floatt unpack(const exprt &, const ieee_float_spect &);

  void round_fraction(unbiased_floatt &result, const rounding_mode_bitst &, const ieee_float_spect &);
  void round_exponent(unbiased_floatt &result, const rounding_mode_bitst &, const ieee_float_spect &);
  
  // rounding decision for fraction
  exprt fraction_rounding_decision(
    const unsigned dest_bits,
    const exprt sign,
    const exprt &fraction,
    const rounding_mode_bitst &);

  // helpers for adder

  // computes src1.exponent-src2.exponent with extension
  exprt subtract_exponents(
    const unbiased_floatt &src1,
    const unbiased_floatt &src2);

  // computes the "sticky-bit"
  exprt sticky_right_shift(
    const exprt &op,
    const exprt &dist,
    exprt &sticky);
};

static inline exprt float_bv(const exprt &src)
{
  return float_bvt()(src);
}

#endif
