/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/std_types.h>

#include <solvers/floatbv/float_utils.h>

#include <algorithm>
#include <iterator>

#include "boolbv_type.h"

bvt boolbvt::convert_unary_minus(const unary_minus_exprt &expr)
{
  const typet &type=ns.follow(expr.type());

  std::size_t width=boolbv_width(type);

  if(width==0)
    return conversion_failed(expr);

  const exprt &op = expr.op();

  const bvt &op_bv = convert_bv(op, width);

  bvtypet bvtype=get_bvtype(type);
  bvtypet op_bvtype = get_bvtype(op.type());

  if(bvtype==bvtypet::IS_UNKNOWN &&
     (type.id()==ID_vector || type.id()==ID_complex))
  {
    const typet &subtype=ns.follow(type.subtype());

    std::size_t sub_width=boolbv_width(subtype);

    INVARIANT(
      sub_width > 0,
      "bitvector representation of type needs to have at least one bit");

    INVARIANT(
      width % sub_width == 0,
      "total bitvector width needs to be a multiple of the component bitvector "
      "widths");

    bvt bv;

    for(std::size_t sub_idx = 0; sub_idx < width; sub_idx += sub_width)
    {
      bvt tmp_op;

      const auto sub_it = std::next(op_bv.begin(), sub_idx);
      std::copy_n(sub_it, sub_width, std::back_inserter(tmp_op));

      if(type.subtype().id() == ID_floatbv)
      {
        float_utilst float_utils(prop, to_floatbv_type(subtype));
        tmp_op = float_utils.negate(tmp_op);
      }
      else
        tmp_op = bv_utils.negate(tmp_op);

      INVARIANT(
        tmp_op.size() == sub_width,
        "bitvector after negation shall have same bit width");

      std::copy(tmp_op.begin(), tmp_op.end(), std::back_inserter(bv));
    }

    return bv;
  }
  else if(bvtype==bvtypet::IS_FIXED && op_bvtype==bvtypet::IS_FIXED)
  {
    return bv_utils.negate(op_bv);
  }
  else if(bvtype==bvtypet::IS_FLOAT && op_bvtype==bvtypet::IS_FLOAT)
  {
    float_utilst float_utils(prop, to_floatbv_type(expr.type()));
    return float_utils.negate(op_bv);
  }
  else if((op_bvtype==bvtypet::IS_SIGNED || op_bvtype==bvtypet::IS_UNSIGNED) &&
          (bvtype==bvtypet::IS_SIGNED || bvtype==bvtypet::IS_UNSIGNED))
  {
    return bv_utils.negate(op_bv);
  }

  return conversion_failed(expr);
}
