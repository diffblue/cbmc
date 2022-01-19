/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/bitvector_types.h>
#include <util/invariant.h>

#include <solvers/floatbv/float_utils.h>

bvt boolbvt::convert_add_sub(const exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_plus || expr.id() == ID_minus ||
    expr.id() == "no-overflow-plus" || expr.id() == "no-overflow-minus");

  const typet &type = expr.type();

  if(type.id()!=ID_unsignedbv &&
     type.id()!=ID_signedbv &&
     type.id()!=ID_fixedbv &&
     type.id()!=ID_floatbv &&
     type.id()!=ID_range &&
     type.id()!=ID_complex &&
     type.id()!=ID_vector)
    return conversion_failed(expr);

  std::size_t width=boolbv_width(type);

  if(width==0)
    return conversion_failed(expr);

  const exprt::operandst &operands=expr.operands();

  DATA_INVARIANT(
    !operands.empty(),
    "operator " + expr.id_string() + " takes at least one operand");

  const exprt &op0 = to_multi_ary_expr(expr).op0();
  DATA_INVARIANT(
    op0.type() == type, "add/sub with mixed types:\n" + expr.pretty());

  bvt bv = convert_bv(op0, width);

  bool subtract=(expr.id()==ID_minus ||
                 expr.id()=="no-overflow-minus");

  bool no_overflow=(expr.id()=="no-overflow-plus" ||
                    expr.id()=="no-overflow-minus");

  typet arithmetic_type = (type.id() == ID_vector || type.id() == ID_complex)
                            ? to_type_with_subtype(type).subtype()
                            : type;

  bv_utilst::representationt rep=
    (arithmetic_type.id()==ID_signedbv ||
     arithmetic_type.id()==ID_fixedbv)?bv_utilst::representationt::SIGNED:
                                       bv_utilst::representationt::UNSIGNED;

  for(exprt::operandst::const_iterator
      it=operands.begin()+1;
      it!=operands.end(); it++)
  {
    DATA_INVARIANT(
      it->type() == type, "add/sub with mixed types:\n" + expr.pretty());

    const bvt &op = convert_bv(*it, width);

    if(type.id()==ID_vector || type.id()==ID_complex)
    {
      std::size_t sub_width =
        boolbv_width(to_type_with_subtype(type).subtype());

      INVARIANT(sub_width != 0, "vector elements shall have nonzero bit width");
      INVARIANT(
        width % sub_width == 0,
        "total vector bit width shall be a multiple of the element bit width");

      std::size_t size=width/sub_width;
      bv.resize(width);

      for(std::size_t i=0; i<size; i++)
      {
        bvt tmp_op;
        tmp_op.resize(sub_width);

        for(std::size_t j=0; j<tmp_op.size(); j++)
        {
          const std::size_t index = i * sub_width + j;
          INVARIANT(index < op.size(), "bit index shall be within bounds");
          tmp_op[j] = op[index];
        }

        bvt tmp_result;
        tmp_result.resize(sub_width);

        for(std::size_t j=0; j<tmp_result.size(); j++)
        {
          const std::size_t index = i * sub_width + j;
          INVARIANT(index < bv.size(), "bit index shall be within bounds");
          tmp_result[j] = bv[index];
        }

        if(to_type_with_subtype(type).subtype().id() == ID_floatbv)
        {
          // needs to change due to rounding mode
          float_utilst float_utils(
            prop, to_floatbv_type(to_type_with_subtype(type).subtype()));
          tmp_result=float_utils.add_sub(tmp_result, tmp_op, subtract);
        }
        else
          tmp_result=bv_utils.add_sub(tmp_result, tmp_op, subtract);

        INVARIANT(
          tmp_result.size() == sub_width,
          "applying the add/sub operation shall not change the bitwidth");

        for(std::size_t j=0; j<tmp_result.size(); j++)
        {
          const std::size_t index = i * sub_width + j;
          INVARIANT(index < bv.size(), "bit index shall be within bounds");
          bv[index] = tmp_result[j];
        }
      }
    }
    else if(type.id()==ID_floatbv)
    {
      // needs to change due to rounding mode
      float_utilst float_utils(prop, to_floatbv_type(arithmetic_type));
      bv=float_utils.add_sub(bv, op, subtract);
    }
    else if(no_overflow)
      bv=bv_utils.add_sub_no_overflow(bv, op, subtract, rep);
    else
      bv=bv_utils.add_sub(bv, op, subtract);
  }

  return bv;
}
