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

protected:
  // helpers
  exprt exponent_all_ones(const exprt &, const ieee_float_spect &spec);
  exprt exponent_all_zeros(const exprt &, const ieee_float_spect &spec);
  exprt fraction_all_zeros(const exprt &, const ieee_float_spect &spec);

  exprt negation(const exprt &, const ieee_float_spect &);
  exprt abs(const exprt &, const ieee_float_spect &);
  exprt is_equal(const exprt &, const exprt &, const ieee_float_spect &);
  exprt is_zero(const exprt &, const ieee_float_spect &);
  exprt isnan(const exprt &, const ieee_float_spect &);
  exprt isinf(const exprt &, const ieee_float_spect &);
  exprt isnormal(const exprt &, const ieee_float_spect &);
  exprt isfinite(const exprt &, const ieee_float_spect &);

  ieee_float_spect get_spec(const exprt &);
  
  inline constant_exprt uint_const(unsigned u)
  {
    return constant_exprt(i2string(u), typet(ID_integer));
  }
  
  // add/sub
  exprt add_sub(bool subtract, const exprt &, const exprt &, const exprt &rm, const ieee_float_spect &);
  
  // mul/div
  exprt mul(const exprt &, const exprt &, const exprt &rm, const ieee_float_spect &);
  exprt div(const exprt &, const exprt &, const exprt &rm, const ieee_float_spect &);

  // conversion
  exprt from_unsigned_integer(const exprt &, const exprt &rm, const ieee_float_spect &);
  exprt from_signed_integer(const exprt &, const exprt &rm, const ieee_float_spect &);
  exprt to_signed_integer(const exprt &src, unsigned int_width, const exprt &rm, const ieee_float_spect &);
  exprt to_unsigned_integer(const exprt &src, unsigned int_width, const exprt &rm, const ieee_float_spect &);
  exprt conversion(const exprt &src, const exprt &rm, const ieee_float_spect &src_spec, const ieee_float_spect &dest_spec);

  // relations
  typedef enum { LT, LE, EQ, GT, GE } relt;
  exprt relation(const exprt &, relt rel, const exprt &, const ieee_float_spect &);
};

#endif
