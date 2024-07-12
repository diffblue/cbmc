/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/floatbv_expr.h>

#include <solvers/floatbv/float_utils.h>

#include "boolbv.h"

bvt boolbvt::convert_floatbv_typecast(const floatbv_typecast_exprt &expr)
{
  const exprt &op0=expr.op(); // number to convert
  const exprt &op1=expr.rounding_mode(); // rounding mode

  bvt bv0=convert_bv(op0);
  bvt bv1=convert_bv(op1);

  const typet &src_type = expr.op0().type();
  const typet &dest_type = expr.type();

  if(src_type==dest_type) // redundant type cast?
    return bv0;

  if(src_type.id() == ID_c_bit_field)
  {
    // go through underlying type
    return convert_floatbv_typecast(floatbv_typecast_exprt(
      typecast_exprt(op0, to_c_bit_field_type(src_type).underlying_type()),
      op1,
      dest_type));
  }

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

bvt boolbvt::convert_floatbv_op(const ieee_float_op_exprt &expr)
{
  const exprt &lhs = expr.lhs();
  const exprt &rhs = expr.rhs();
  const exprt &rounding_mode = expr.rounding_mode();

  bvt lhs_as_bv = convert_bv(lhs);
  bvt rhs_as_bv = convert_bv(rhs);
  bvt rounding_mode_as_bv = convert_bv(rounding_mode);

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    lhs.type() == expr.type() && rhs.type() == expr.type(),
    "both operands of a floating point operator must match the expression type",
    irep_pretty_diagnosticst{expr});

  float_utilst float_utils(prop);

  float_utils.set_rounding_mode(rounding_mode_as_bv);

  if(expr.type().id() == ID_floatbv)
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
    else
      UNREACHABLE;
  }
  else if(expr.type().id() == ID_complex)
  {
    const typet &subtype = to_type_with_subtype(expr.type()).subtype();

    if(subtype.id()==ID_floatbv)
    {
      float_utils.spec=ieee_float_spect(to_floatbv_type(subtype));

      std::size_t width = boolbv_width(expr.type());
      std::size_t sub_width=boolbv_width(subtype);

      DATA_INVARIANT(
        sub_width > 0 && width % sub_width == 0,
        "width of a complex subtype must be positive and evenly divide the "
        "width of the complex expression");
      DATA_INVARIANT(
        sub_width * 2 == width, "a complex type consists of exactly two parts");

      bvt lhs_real{lhs_as_bv.begin(), lhs_as_bv.begin() + sub_width};
      bvt rhs_real{rhs_as_bv.begin(), rhs_as_bv.begin() + sub_width};

      bvt lhs_imag{lhs_as_bv.begin() + sub_width, lhs_as_bv.end()};
      bvt rhs_imag{rhs_as_bv.begin() + sub_width, rhs_as_bv.end()};

      bvt result_real, result_imag;

      if(expr.id() == ID_floatbv_plus || expr.id() == ID_floatbv_minus)
      {
        result_real = float_utils.add_sub(
          lhs_real, rhs_real, expr.id() == ID_floatbv_minus);
        result_imag = float_utils.add_sub(
          lhs_imag, rhs_imag, expr.id() == ID_floatbv_minus);
      }
      else if(expr.id() == ID_floatbv_mult)
      {
        // Could be optimised to just three multiplications with more additions
        // instead, but then we'd have to worry about the impact of possible
        // overflows. So we use the naive approach for now:
        result_real = float_utils.add_sub(
          float_utils.mul(lhs_real, rhs_real),
          float_utils.mul(lhs_imag, rhs_imag),
          true);
        result_imag = float_utils.add_sub(
          float_utils.mul(lhs_real, rhs_imag),
          float_utils.mul(lhs_imag, rhs_real),
          false);
      }
      else if(expr.id() == ID_floatbv_div)
      {
        bvt numerator_real = float_utils.add_sub(
          float_utils.mul(lhs_real, rhs_real),
          float_utils.mul(lhs_imag, rhs_imag),
          false);
        bvt numerator_imag = float_utils.add_sub(
          float_utils.mul(lhs_imag, rhs_real),
          float_utils.mul(lhs_real, rhs_imag),
          true);

        bvt denominator = float_utils.add_sub(
          float_utils.mul(rhs_real, rhs_real),
          float_utils.mul(rhs_imag, rhs_imag),
          false);

        result_real = float_utils.div(numerator_real, denominator);
        result_imag = float_utils.div(numerator_imag, denominator);
      }
      else
        UNREACHABLE;

      bvt result_bv = std::move(result_real);
      result_bv.reserve(width);
      result_bv.insert(
        result_bv.end(),
        std::make_move_iterator(result_imag.begin()),
        std::make_move_iterator(result_imag.end()));

      return result_bv;
    }
    else
      return conversion_failed(expr);
  }
  else
    return conversion_failed(expr);
}
