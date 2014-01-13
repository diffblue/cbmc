/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

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
//  else if(src.id()==ID_ieee_float_equal)
//    return convert_ieee_float_equal(to_ieee_float_equal_expr(src));

  return nil_exprt();
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
  const floatbv_typet &type=to_floatbv_type(src.type());
  unsigned width=type.get_width();
  
  std::string mask_str;
  mask_str.resize(width, '1');
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
  const floatbv_typet &type=to_floatbv_type(src.type());
  unsigned width=type.get_width();
  
  std::string mask_str;
  mask_str.resize(width, '0');
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
  return nil_exprt();
}

/*******************************************************************\

Function: float_bvt::convert_ieee_float_notequal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

//exprt float_bvt::convert_ieee_float_notequal(const ieee_float_notequal_exprt &src)
//{
//}
