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
  unsignedbv_typet exponent_type(spec.e);

  extractbits_exprt exponent(
    src, uint_const(spec.f+spec.e-1), uint_const(spec.f), exponent_type);

  return equal_exprt(exponent, exponent_type.largest_expr());
}

/*******************************************************************\

Function: float_bvt::exponent_all_zeros

  Inputs:

 Outputs:
D
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
}

/*******************************************************************\

Function: float_bvt::relation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::from_signed_integer(
  const exprt &src,
  const exprt &rm,
  const ieee_float_spect &spec)
{
}

/*******************************************************************\

Function: float_bvt::relation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::to_signed_integer(
  const exprt &src,
  unsigned int_width,
  const exprt &rm,
  const ieee_float_spect &spec)
{
}

/*******************************************************************\

Function: float_bvt::relation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::to_unsigned_integer(
  const exprt &src,
  unsigned int_width,
  const exprt &rm,
  const ieee_float_spect &)
{
}

/*******************************************************************\

Function: float_bvt::relation

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
}

/*******************************************************************\

Function: float_bvt::relation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt float_bvt::relation(
  const exprt &op0,
  relt rel,
  const exprt &op1,
  const ieee_float_spect &spec)
{
}

