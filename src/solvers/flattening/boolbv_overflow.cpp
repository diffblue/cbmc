/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/invariant.h>
#include <util/prefix.h>
#include <util/string2int.h>

literalt boolbvt::convert_overflow(const exprt &expr)
{
  const exprt::operandst &operands=expr.operands();

  if(expr.id()==ID_overflow_plus ||
     expr.id()==ID_overflow_minus)
  {
    DATA_INVARIANT(
      operands.size() == 2,
      "expression " + expr.id_string() + " should have two operands");

    const bvt &bv0=convert_bv(operands[0]);
    const bvt &bv1=convert_bv(operands[1]);

    if(bv0.size()!=bv1.size())
      return SUB::convert_rest(expr);

    bv_utilst::representationt rep=
      expr.op0().type().id()==ID_signedbv?bv_utilst::representationt::SIGNED:
                                          bv_utilst::representationt::UNSIGNED;

    return expr.id()==ID_overflow_minus?
      bv_utils.overflow_sub(bv0, bv1, rep):
      bv_utils.overflow_add(bv0, bv1, rep);
  }
  else if(expr.id()==ID_overflow_mult)
  {
    DATA_INVARIANT(
      operands.size() == 2,
      "overflow_mult expression should have two operands");

    if(operands[0].type().id()!=ID_unsignedbv &&
       operands[0].type().id()!=ID_signedbv)
      return SUB::convert_rest(expr);

    bvt bv0=convert_bv(operands[0]);
    bvt bv1 = convert_bv(operands[1], bv0.size());

    bv_utilst::representationt rep=
      operands[0].type().id()==ID_signedbv?bv_utilst::representationt::SIGNED:
                                           bv_utilst::representationt::UNSIGNED;

    DATA_INVARIANT(
      operands[0].type() == operands[1].type(),
      "operands of overflow_mult expression shall have same type");

    std::size_t old_size=bv0.size();
    std::size_t new_size=old_size*2;

    // sign/zero extension
    bv0=bv_utils.extension(bv0, new_size, rep);
    bv1=bv_utils.extension(bv1, new_size, rep);

    bvt result=bv_utils.multiplier(bv0, bv1, rep);

    if(rep==bv_utilst::representationt::UNSIGNED)
    {
      bvt bv_overflow;
      bv_overflow.reserve(old_size);

      // get top result bits
      for(std::size_t i=old_size; i<result.size(); i++)
        bv_overflow.push_back(result[i]);

      return prop.lor(bv_overflow);
    }
    else
    {
      bvt bv_overflow;
      bv_overflow.reserve(old_size);

      // get top result bits, plus one more
      DATA_INVARIANT(old_size!=0, "zero-size operand");
      for(std::size_t i=old_size-1; i<result.size(); i++)
        bv_overflow.push_back(result[i]);

      // these need to be either all 1's or all 0's
      literalt all_one=prop.land(bv_overflow);
      literalt all_zero=!prop.lor(bv_overflow);
      return !prop.lor(all_one, all_zero);
    }
  }
  else if(expr.id() == ID_overflow_shl)
  {
    DATA_INVARIANT(
      operands.size() == 2, "overflow_shl expression should have two operands");

    const bvt &bv0=convert_bv(operands[0]);
    const bvt &bv1=convert_bv(operands[1]);

    std::size_t old_size = bv0.size();
    std::size_t new_size = old_size * 2;

    bv_utilst::representationt rep=
      operands[0].type().id()==ID_signedbv?bv_utilst::representationt::SIGNED:
                                           bv_utilst::representationt::UNSIGNED;

    bvt bv_ext=bv_utils.extension(bv0, new_size, rep);

    bvt result=bv_utils.shift(bv_ext, bv_utilst::shiftt::SHIFT_LEFT, bv1);

    // a negative shift is undefined; yet this isn't an overflow
    literalt neg_shift =
      operands[1].type().id() == ID_unsignedbv ?
        const_literal(false) :
        bv1.back(); // sign bit

    // an undefined shift of a non-zero value always results in overflow; the
    // use of unsigned comparision is safe here as we cover the signed negative
    // case via neg_shift
    literalt undef =
      bv_utils.rel(
        bv1,
        ID_gt,
        bv_utils.build_constant(old_size, bv1.size()),
        bv_utilst::representationt::UNSIGNED);

    literalt overflow;

    if(rep == bv_utilst::representationt::UNSIGNED)
    {
      // get top result bits
      result.erase(result.begin(), result.begin() + old_size);

      // one of the top bits is non-zero
      overflow=prop.lor(result);
    }
    else
    {
      // get top result bits plus sign bit
      DATA_INVARIANT(old_size != 0, "zero-size operand");
      result.erase(result.begin(), result.begin() + old_size - 1);

      // the sign bit has changed
      literalt sign_change=!prop.lequal(bv0.back(), result.front());

      // these need to be either all 1's or all 0's
      literalt all_one=prop.land(result);
      literalt all_zero=!prop.lor(result);

      overflow=prop.lor(sign_change, !prop.lor(all_one, all_zero));
    }

    // a negative shift isn't an overflow; else check the conditions built
    // above
    return
      prop.land(!neg_shift, prop.lselect(undef, prop.lor(bv0), overflow));
  }
  else if(expr.id()==ID_overflow_unary_minus)
  {
    DATA_INVARIANT(
      operands.size() == 1,
      "overflow_unary_minus expression should have one operand");

    const bvt &bv=convert_bv(operands[0]);

    return bv_utils.overflow_negate(bv);
  }
  else if(has_prefix(expr.id_string(), "overflow-typecast-"))
  {
    std::size_t bits=unsafe_string2unsigned(id2string(expr.id()).substr(18));
    INVARIANT(bits != 0, "");

    const exprt::operandst &operands=expr.operands();

    DATA_INVARIANT(
      operands.size() == 1,
      "expression " + expr.id_string() + " should have one operand");

    const exprt &op=operands[0];

    const bvt &bv=convert_bv(op);

    INVARIANT(bits < bv.size(), "");

    // signed or unsigned?
    if(op.type().id()==ID_signedbv)
    {
      bvt tmp_bv;
      for(std::size_t i=bits; i<bv.size(); i++)
        tmp_bv.push_back(prop.lxor(bv[bits-1], bv[i]));

      return prop.lor(tmp_bv);
    }
    else
    {
      bvt tmp_bv;
      for(std::size_t i=bits; i<bv.size(); i++)
        tmp_bv.push_back(bv[i]);

      return prop.lor(tmp_bv);
    }
  }

  return SUB::convert_rest(expr);
}
