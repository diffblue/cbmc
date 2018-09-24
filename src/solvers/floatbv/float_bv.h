/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_FLOATBV_FLOAT_BV_H
#define CPROVER_SOLVERS_FLOATBV_FLOAT_BV_H

#include <util/ieee_float.h>
#include <util/std_expr.h>

#include <solvers/flattening/bv_utils.h>

class float_bvt
{
public:
  exprt operator()(const exprt &src) const
  {
    return convert(src);
  }

  exprt convert(const exprt &) const;

  static exprt negation(const exprt &, const ieee_float_spect &);
  static exprt abs(const exprt &, const ieee_float_spect &);
  static exprt is_equal(const exprt &, const exprt &, const ieee_float_spect &);
  static exprt is_zero(const exprt &);
  static exprt isnan(const exprt &, const ieee_float_spect &);
  static exprt isinf(const exprt &, const ieee_float_spect &);
  static exprt isnormal(const exprt &, const ieee_float_spect &);
  static exprt isfinite(const exprt &, const ieee_float_spect &);

  // add/sub
  exprt add_sub(
    bool subtract,
    const exprt &,
    const exprt &,
    const exprt &rm,
    const ieee_float_spect &) const;

  // mul/div
  exprt
  mul(const exprt &, const exprt &, const exprt &rm, const ieee_float_spect &)
    const;
  exprt
  div(const exprt &, const exprt &, const exprt &rm, const ieee_float_spect &)
    const;

  // conversion
  exprt from_unsigned_integer(
    const exprt &,
    const exprt &rm,
    const ieee_float_spect &) const;
  exprt from_signed_integer(
    const exprt &,
    const exprt &rm,
    const ieee_float_spect &) const;
  static exprt to_signed_integer(
    const exprt &src,
    std::size_t dest_width,
    const exprt &rm,
    const ieee_float_spect &);
  static exprt to_unsigned_integer(
    const exprt &src,
    std::size_t dest_width,
    const exprt &rm,
    const ieee_float_spect &);
  static exprt to_integer(
    const exprt &src,
    std::size_t dest_width,
    bool is_signed,
    const exprt &rm,
    const ieee_float_spect &);
  exprt conversion(
    const exprt &src,
    const exprt &rm,
    const ieee_float_spect &src_spec,
    const ieee_float_spect &dest_spec) const;

  // relations
  enum class relt { LT, LE, EQ, GT, GE };
  static exprt
  relation(const exprt &, relt rel, const exprt &, const ieee_float_spect &);

private:
  // helpers
  static ieee_float_spect get_spec(const exprt &);
  // still biased
  static exprt get_exponent(const exprt &, const ieee_float_spect &);
  // without hidden bit
  static exprt get_fraction(const exprt &, const ieee_float_spect &);
  static exprt sign_bit(const exprt &);

  static exprt exponent_all_ones(const exprt &, const ieee_float_spect &);
  static exprt exponent_all_zeros(const exprt &, const ieee_float_spect &);
  static exprt fraction_all_zeros(const exprt &, const ieee_float_spect &);

  struct rounding_mode_bitst
  {
    // these are mutually exclusive, obviously
    exprt round_to_even;
    exprt round_to_zero;
    exprt round_to_plus_inf;
    exprt round_to_minus_inf;

    void get(const exprt &rm);
    explicit rounding_mode_bitst(const exprt &rm) { get(rm); }
  };

  // unpacked
  static void normalization_shift(exprt &fraction, exprt &exponent);
  static void denormalization_shift(
    exprt &fraction,
    exprt &exponent,
    const ieee_float_spect &);

  static exprt add_bias(const exprt &exponent, const ieee_float_spect &);
  static exprt sub_bias(const exprt &exponent, const ieee_float_spect &);

  static exprt limit_distance(const exprt &dist, mp_integer limit);

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

  static biased_floatt bias(const unbiased_floatt &, const ieee_float_spect &);

  // this takes unpacked format, and returns packed
  exprt rounder(
    const unbiased_floatt &,
    const exprt &rm,
    const ieee_float_spect &) const;
  static exprt pack(const biased_floatt &, const ieee_float_spect &);
  static unbiased_floatt unpack(const exprt &, const ieee_float_spect &);

  static void round_fraction(
    unbiased_floatt &result,
    const rounding_mode_bitst &,
    const ieee_float_spect &);
  static void round_exponent(
    unbiased_floatt &result,
    const rounding_mode_bitst &,
    const ieee_float_spect &);

  // rounding decision for fraction
  static exprt fraction_rounding_decision(
    const std::size_t dest_bits,
    const exprt sign,
    const exprt &fraction,
    const rounding_mode_bitst &);

  // helpers for adder

  // computes src1.exponent-src2.exponent with extension
  static exprt
  subtract_exponents(const unbiased_floatt &src1, const unbiased_floatt &src2);

  // computes the "sticky-bit"
  static exprt
  sticky_right_shift(const exprt &op, const exprt &dist, exprt &sticky);
};

inline exprt float_bv(const exprt &src)
{
  return float_bvt()(src);
}

#endif // CPROVER_SOLVERS_FLOATBV_FLOAT_BV_H
