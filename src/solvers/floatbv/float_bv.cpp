/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/expr_util.h>
#include <util/std_expr.h>

#include "float_bv.h"

/*******************************************************************\

Function: float_bvt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::convert(const exprt &src)
{
  if(src.id()==ID_abs)
    return convert_abs(to_abs_expr(src));
  else if(src.id()==ID_unary_minus)
    return convert_unary_minus(to_unary_minus_expr(src));
  else if(src.id()==ID_ieee_float_equal)
    return convert_ieee_float_equal(to_ieee_float_equal_expr(src));
  else if(src.id()==ID_ieee_float_notequal)
    return convert_ieee_float_notequal(to_ieee_float_notequal_expr(src));
  else if(src.id()==ID_floatbv_typecast)
    return convert_floatbv_typecast(to_floatbv_typecast_expr(src));
  else if(src.id()==ID_floatbv_plus)
    return convert_floatbv_plus(to_ieee_float_op_expr(src));
  else if(src.id()==ID_floatbv_minus)
    return convert_floatbv_minus(to_ieee_float_op_expr(src));
  else if(src.id()==ID_floatbv_mult)
    return convert_floatbv_mult(to_ieee_float_op_expr(src));
  else if(src.id()==ID_floatbv_div)
    return convert_floatbv_div(to_ieee_float_op_expr(src));
  else if(src.id()==ID_isnan)
    return convert_isnan(to_isnan_expr(src));
  else if(src.id()==ID_isfinite)
    return convert_isfinite(to_isfinite_expr(src));
  else if(src.id()==ID_isinf)
    return convert_isinf(to_isinf_expr(src));
  else if(src.id()==ID_isnormal)
    return convert_isnormal(to_isnormal_expr(src));
  else
    return nil_exprt();
}

/*******************************************************************\

Function: float_bvt::get_spec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ieee_float_spect float_bvt::get_spec(const exprt &src)
{
  const floatbv_typet &type=to_floatbv_type(src.type());
  return ieee_float_spect(type);
}

/*******************************************************************\

Function: float_bvt::convert_abs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::convert_abs(const abs_exprt &src)
{
  // we mask away the sign bit, which is the most significand bit
  std::string mask_str;
  mask_str.resize(get_spec(src).width(), '1');
  mask_str[0]='0';
  
  constant_exprt mask(mask_str, src.type());
  
  return bitand_exprt(src.op(), mask);
}

/*******************************************************************\

Function: float_bvt::convert_unary_minus

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::convert_unary_minus(const unary_minus_exprt &src)
{
  // we flip the sign bit with an xor
  std::string mask_str;
  mask_str.resize(get_spec(src).width(), '0');
  mask_str[0]='1';
  
  constant_exprt mask(mask_str, src.type());
  
  return bitxor_exprt(src.op(), mask);
}

/*******************************************************************\

Function: float_bvt::convert_ieee_float_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::convert_ieee_float_equal(const ieee_float_equal_exprt &src)
{
  return is_equal(src.op0(), src.op1(), get_spec(src.op0()));
}

/*******************************************************************\

Function: float_bvt::convert_ieee_float_notequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::convert_ieee_float_notequal(
  const ieee_float_notequal_exprt &src)
{
  return not_exprt(
    is_equal(src.op0(), src.op1(), get_spec(src.op0())));
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
  exprt is_NaN0=is_NaN(src0, spec);
  exprt is_NaN1=is_NaN(src1, spec);
  exprt NaN=or_exprt(is_NaN0, is_NaN1);

  exprt bitwise_equal=equal_exprt(src0, src1);

  return and_exprt(
    or_exprt(bitwise_equal, both_zero),
    not_exprt(NaN));
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
  unsignedbv_typet exponent_type(spec.e);

  extractbits_exprt exponent(
    src, uint_const(spec.f+spec.e-1), uint_const(spec.f), exponent_type);

  return equal_exprt(exponent, exponent_type.largest_expr());
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
  unsignedbv_typet exponent_type(spec.e);

  extractbits_exprt exponent(
    src, uint_const(spec.f+spec.e-1), uint_const(spec.f), exponent_type);

  return equal_exprt(exponent, exponent_type.zero_expr());
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
  unsignedbv_typet fraction_type(spec.e);

  extractbits_exprt fraction(
    src, uint_const(spec.f-1), uint_const(0), fraction_type);

  return equal_exprt(fraction, fraction_type.zero_expr());
}

