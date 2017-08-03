/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <cassert>

#include <util/prefix.h>
#include <util/string2int.h>

literalt boolbvt::convert_overflow(const exprt &expr)
{
  const exprt::operandst &operands=expr.operands();

  if(expr.id()==ID_overflow_plus ||
     expr.id()==ID_overflow_minus)
  {
    if(operands.size()!=2)
      throw "operator "+expr.id_string()+" takes two operands";

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
    if(operands.size()!=2)
      throw "operator "+expr.id_string()+" takes two operands";

    if(operands[0].type().id()!=ID_unsignedbv &&
       operands[0].type().id()!=ID_signedbv)
      return SUB::convert_rest(expr);

    bvt bv0=convert_bv(operands[0]);
    bvt bv1=convert_bv(operands[1]);

    if(bv0.size()!=bv1.size())
      throw "operand size mismatch on overflow-*";

    bv_utilst::representationt rep=
      operands[0].type().id()==ID_signedbv?bv_utilst::representationt::SIGNED:
                                           bv_utilst::representationt::UNSIGNED;

    if(operands[0].type()!=operands[1].type())
      throw "operand type mismatch on overflow-*";

    assert(bv0.size()==bv1.size());
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
      assert(old_size!=0);
      for(std::size_t i=old_size-1; i<result.size(); i++)
        bv_overflow.push_back(result[i]);

      // these need to be either all 1's or all 0's
      literalt all_one=prop.land(bv_overflow);
      literalt all_zero=!prop.lor(bv_overflow);
      return !prop.lor(all_one, all_zero);
    }
  }
  else if(expr.id()==ID_overflow_unary_minus)
  {
    if(operands.size()!=1)
      throw "operator "+expr.id_string()+" takes one operand";

    const bvt &bv=convert_bv(operands[0]);

    return bv_utils.overflow_negate(bv);
  }
  else if(has_prefix(expr.id_string(), "overflow-typecast-"))
  {
    std::size_t bits=unsafe_string2unsigned(id2string(expr.id()).substr(18));

    const exprt::operandst &operands=expr.operands();

    if(operands.size()!=1)
      throw "operator "+expr.id_string()+" takes one operand";

    const exprt &op=operands[0];

    const bvt &bv=convert_bv(op);

    if(bits>=bv.size() || bits==0)
      throw "overflow-typecast got wrong number of bits";

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
