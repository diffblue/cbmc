/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FLOAT_BV_H
#define CPROVER_FLOAT_BV_H

#include <util/i2string.h>
#include <util/ieee_float.h>
#include <util/std_expr.h>

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
  exprt convert_abs(const abs_exprt &);
  exprt convert_unary_minus(const unary_minus_exprt &);
  exprt convert_ieee_float_equal(const ieee_float_equal_exprt &);
  exprt convert_ieee_float_notequal(const ieee_float_notequal_exprt &);
  exprt convert_floatbv_typecast(const floatbv_typecast_exprt &expr);
  exprt convert_floatbv_plus(const ieee_float_op_exprt &expr);
  exprt convert_floatbv_minus(const ieee_float_op_exprt &expr);
  exprt convert_floatbv_mult(const ieee_float_op_exprt &expr);
  exprt convert_floatbv_div(const ieee_float_op_exprt &expr);
  exprt convert_isnan(const isnan_exprt &expr) { return is_NaN(expr.op(), get_spec(expr.op())); }
  exprt convert_isfinite(const isfinite_exprt &);
  exprt convert_isinf(const isinf_exprt &);
  exprt convert_isnormal(const isnormal_exprt &);
  exprt convert_floatbv_rel(const binary_relation_exprt &);

protected:
  // helpers
  exprt exponent_all_ones(const exprt &, const ieee_float_spect &spec);
  exprt exponent_all_zeros(const exprt &, const ieee_float_spect &spec);
  exprt fraction_all_zeros(const exprt &, const ieee_float_spect &spec);
  
  exprt is_equal(const exprt &, const exprt &, const ieee_float_spect &);
  exprt is_zero(const exprt &, const ieee_float_spect &);
  exprt is_NaN(const exprt &, const ieee_float_spect &);

  ieee_float_spect get_spec(const exprt &);
  
  inline constant_exprt uint_const(unsigned u)
  {
    return constant_exprt(i2string(u), typet(ID_integer));
  }

};

#endif
