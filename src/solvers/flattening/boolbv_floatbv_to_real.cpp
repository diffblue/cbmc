/*******************************************************************\

Module:

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Encoding of fp.to_real as a wide signed integer with implicit
/// scaling factor 2^k. The real value is integer_value / 2^k where
/// k = f + bias (sufficient to represent all FP values exactly).

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/ieee_float.h>

#include <solvers/floatbv/float_utils.h>

#include "boolbv.h"

bvt boolbvt::convert_floatbv_to_real(const unary_exprt &expr)
{
  PRECONDITION(expr.id() == ID_floatbv_to_real);
  PRECONDITION(expr.op().type().id() == ID_floatbv);

  const auto &fp_type = to_floatbv_type(expr.op().type());
  const ieee_float_spect spec(fp_type);
  const bvt &src = convert_bv(expr.op());

  float_utilst float_utils(prop, fp_type);

  const std::size_t int_width = boolbv_width(expr.type());
  const std::size_t bias = (1u << (spec.e - 1)) - 1;

  // Extract sign, exponent, fraction from the FP bitvector
  literalt sign = src.back();
  literalt is_zero = float_utils.is_zero(src);
  literalt is_nan = float_utils.is_NaN(src);
  literalt is_inf = float_utils.is_infinity(src);

  // Extract exponent bits and fraction bits
  bvt exp_bits = bv_utils.extract(src, spec.f, spec.f + spec.e - 1);
  bvt frac_bits = bv_utils.extract(src, 0, spec.f - 1);

  // Compute unbiased exponent (signed)
  bvt exp_extended = bv_utils.zero_extension(exp_bits, int_width);
  bvt bias_bv = bv_utils.build_constant(bias, int_width);
  bvt exponent = bv_utils.sub(exp_extended, bias_bv);

  // Build significand with hidden bit
  // For normal: 1.fraction; for subnormal: 0.fraction
  literalt is_normal = float_utils.is_normal(src);
  bvt significand = bv_utils.zero_extension(frac_bits, int_width);
  // Set the hidden bit (bit spec.f) for normal numbers
  significand[spec.f] = is_normal;

  // The real value is: (-1)^sign * significand * 2^(exponent - f)
  // Scaled by 2^(f + bias): result = significand * 2^(exponent + bias)
  // = significand << (exponent + bias)
  // For subnormals: exponent = 1 - bias (not 0 - bias), so
  // shift = 1 - bias + bias = 1. But subnormal significand has no
  // hidden bit, so the value is correct: frac * 2^(1-bias) scaled by
  // 2^(f+bias) = frac * 2^(f+1) = frac << (f+1). But our shift is
  // exponent + bias = (0 - bias) + bias = 0 for subnormals (since
  // exp_bits = 0). That gives frac << 0 = frac, which represents
  // frac / 2^(f+bias). The actual value is frac * 2^(1-bias-f) =
  // frac / 2^(f+bias-1). Off by factor 2.
  // Fix: for subnormals, use exponent = 1 - bias instead of 0 - bias.
  bvt one_bv = bv_utils.build_constant(1, int_width);
  bvt subnormal_exp = bv_utils.sub(one_bv, bias_bv);
  bvt normal_exp = exponent;
  bvt actual_exp = bv_utils.select(is_normal, normal_exp, subnormal_exp);

  // Shift amount = actual_exp + bias = actual_exp + bias
  bvt shift_amount = bv_utils.add(actual_exp, bias_bv);

  // Left-shift the significand
  bvt shifted =
    bv_utils.shift(significand, bv_utilst::shiftt::SHIFT_LEFT, shift_amount);

  // Apply sign: negate if negative
  bvt negated = bv_utils.negate(shifted);
  bvt result = bv_utils.select(sign, negated, shifted);

  // Zero for zero inputs, zero for NaN/infinity (no real representation)
  bvt zero_bv = bv_utils.build_constant(0, int_width);
  result = bv_utils.select(is_zero, zero_bv, result);
  result = bv_utils.select(is_nan, zero_bv, result);
  result = bv_utils.select(is_inf, zero_bv, result);

  return result;
}
