/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <algorithm>
#include <iostream>

#include <util/std_types.h>

#include <solvers/floatbv/float_utils.h>

bvt boolbvt::convert_floatbv_typecast(const floatbv_typecast_exprt &expr)
{
  const exprt &op0=expr.op(); // number to convert
  const exprt &op1=expr.rounding_mode(); // rounding mode

  bvt bv0=convert_bv(op0);
  bvt bv1=convert_bv(op1);

  const typet &src_type=ns.follow(expr.op0().type());
  const typet &dest_type=ns.follow(expr.type());

  if(src_type==dest_type) // redundant type cast?
    return bv0;

  float_utilst float_utils(prop);

  float_utils.set_rounding_mode(convert_bv(op1));

  if(src_type.id()==ID_floatbv &&
     dest_type.id()==ID_floatbv)
  {
    float_utils.spec=ieee_float_spect(to_floatbv_type(src_type));
    return
      float_utils.conversion(
        bv0,
        ieee_float_spect(to_floatbv_type(dest_type)));
  }
  else if(src_type.id()==ID_signedbv &&
          dest_type.id()==ID_floatbv)
  {
    float_utils.spec=ieee_float_spect(to_floatbv_type(dest_type));
    return float_utils.from_signed_integer(bv0);
  }
  else if(src_type.id()==ID_unsignedbv &&
          dest_type.id()==ID_floatbv)
  {
    float_utils.spec=ieee_float_spect(to_floatbv_type(dest_type));
    return float_utils.from_unsigned_integer(bv0);
  }
  else if(src_type.id()==ID_floatbv &&
          dest_type.id()==ID_signedbv)
  {
    std::size_t dest_width=to_signedbv_type(dest_type).get_width();
    float_utils.spec=ieee_float_spect(to_floatbv_type(src_type));
    return float_utils.to_signed_integer(bv0, dest_width);
  }
  else if(src_type.id()==ID_floatbv &&
          dest_type.id()==ID_unsignedbv)
  {
    std::size_t dest_width=to_unsignedbv_type(dest_type).get_width();
    float_utils.spec=ieee_float_spect(to_floatbv_type(src_type));
    return float_utils.to_unsigned_integer(bv0, dest_width);
  }
  else
    return conversion_failed(expr);
}

bvt boolbvt::convert_floatbv_op(const exprt &expr)
{
  const exprt::operandst &operands=expr.operands();

  if(operands.size()!=3)
    throw "operator "+expr.id_string()+" takes three operands";

  const exprt &lhs = expr.op0();
  const exprt &rhs = expr.op1();
  const exprt &rounding_mode = expr.op2();

  bvt lhs_as_bv = convert_bv(lhs);
  bvt rhs_as_bv = convert_bv(rhs);
  bvt rounding_mode_as_bv = convert_bv(rounding_mode);

  const typet &resolved_type = ns.follow(expr.type());
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    lhs.type() == resolved_type && rhs.type() == resolved_type,
    "both operands of a floating point operator must have the same type",
    irep_pretty_diagnosticst{expr});

  float_utilst float_utils(prop);

  float_utils.set_rounding_mode(rounding_mode_as_bv);

  if(resolved_type.id() == ID_floatbv)
  {
    float_utils.spec=ieee_float_spect(to_floatbv_type(expr.type()));

    if(expr.id()==ID_floatbv_plus)
      return float_utils.add_sub(lhs_as_bv, rhs_as_bv, false);
    else if(expr.id()==ID_floatbv_minus)
      return float_utils.add_sub(lhs_as_bv, rhs_as_bv, true);
    else if(expr.id()==ID_floatbv_mult)
      return float_utils.mul(lhs_as_bv, rhs_as_bv);
    else if(expr.id()==ID_floatbv_div)
      return float_utils.div(lhs_as_bv, rhs_as_bv);
    else if(expr.id()==ID_floatbv_rem)
      return float_utils.rem(lhs_as_bv, rhs_as_bv);
    else
      UNREACHABLE;
  }
  else if(resolved_type.id() == ID_vector || resolved_type.id() == ID_complex)
  {
    const typet &subtype = ns.follow(resolved_type.subtype());

    if(subtype.id()==ID_floatbv)
    {
      float_utils.spec=ieee_float_spect(to_floatbv_type(subtype));

      std::size_t width = boolbv_width(resolved_type);
      std::size_t sub_width=boolbv_width(subtype);

      DATA_INVARIANT(
        sub_width > 0 && width % sub_width == 0,
        "width of a vector subtype must be positive and evenly divide the "
        "width of the vector");

      std::size_t size=width/sub_width;
      bvt result_bv;
      result_bv.resize(width);

      for(std::size_t i=0; i<size; i++)
      {
        bvt lhs_sub_bv, rhs_sub_bv, sub_result_bv;

        lhs_sub_bv.assign(
          lhs_as_bv.begin() + i * sub_width,
          lhs_as_bv.begin() + (i + 1) * sub_width);
        rhs_sub_bv.assign(
          rhs_as_bv.begin() + i * sub_width,
          rhs_as_bv.begin() + (i + 1) * sub_width);

        if(expr.id()==ID_floatbv_plus)
          sub_result_bv = float_utils.add_sub(lhs_sub_bv, rhs_sub_bv, false);
        else if(expr.id()==ID_floatbv_minus)
          sub_result_bv = float_utils.add_sub(lhs_sub_bv, rhs_sub_bv, true);
        else if(expr.id()==ID_floatbv_mult)
          sub_result_bv = float_utils.mul(lhs_sub_bv, rhs_sub_bv);
        else if(expr.id()==ID_floatbv_div)
          sub_result_bv = float_utils.div(lhs_sub_bv, rhs_sub_bv);
        else
          UNREACHABLE;

        INVARIANT(
          sub_result_bv.size() == sub_width,
          "we constructed a new vector of the right size");
        INVARIANT(
          i * sub_width + sub_width - 1 < result_bv.size(),
          "the sub-bitvector fits into the result bitvector");
        std::copy(
          sub_result_bv.begin(),
          sub_result_bv.end(),
          result_bv.begin() + i * sub_width);
      }

      return result_bv;
    }
    else
      return conversion_failed(expr);
  }
  else
    return conversion_failed(expr);
}
