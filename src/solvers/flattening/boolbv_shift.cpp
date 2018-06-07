/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <limits>

#include <util/arith_tools.h>

bvt boolbvt::convert_shift(const binary_exprt &expr)
{
  const irep_idt &type_id=expr.type().id();

  if(type_id!=ID_unsignedbv &&
     type_id!=ID_signedbv &&
     type_id!=ID_floatbv &&
     type_id!=ID_pointer &&
     type_id!=ID_bv &&
     type_id!=ID_verilog_signedbv &&
     type_id!=ID_verilog_unsignedbv)
    return conversion_failed(expr);

  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  const bvt &op = convert_bv(expr.op0(), width);

  bv_utilst::shiftt shift;

  if(expr.id()==ID_shl)
    shift=bv_utilst::shiftt::SHIFT_LEFT;
  else if(expr.id()==ID_ashr)
    shift=bv_utilst::shiftt::SHIFT_ARIGHT;
  else if(expr.id()==ID_lshr)
    shift=bv_utilst::shiftt::SHIFT_LRIGHT;
  else if(expr.id()==ID_rol)
    shift=bv_utilst::shiftt::ROTATE_LEFT;
  else if(expr.id()==ID_ror)
    shift=bv_utilst::shiftt::ROTATE_RIGHT;
  else
    UNREACHABLE;

  // we allow a constant as shift distance

  if(expr.op1().is_constant())
  {
    mp_integer i = numeric_cast_v<mp_integer>(expr.op1());

    std::size_t distance;

    if(i<0 || i>std::numeric_limits<signed>::max())
      distance=0;
    else
      distance = numeric_cast_v<std::size_t>(i);

    if(type_id==ID_verilog_signedbv ||
       type_id==ID_verilog_unsignedbv)
      distance*=2;

    return bv_utils.shift(op, shift, distance);
  }
  else
  {
    const bvt &distance=convert_bv(expr.op1());
    return bv_utils.shift(op, shift, distance);
  }
}
