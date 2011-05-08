/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stdlib.h>
#include <assert.h>

#include <prefix.h>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_overflow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolbvt::convert_overflow(const exprt &expr)
{
  const exprt::operandst &operands=expr.operands();

  if(expr.id()==ID_overflow_plus ||
     expr.id()==ID_overflow_minus)
  {
    if(operands.size()!=2)
      throw "operand "+expr.id_string()+" takes two operands";

    bvt bv0, bv1;

    convert_bv(operands[0], bv0);
    convert_bv(operands[1], bv1);

    if(bv0.size()!=bv1.size())
      return SUB::convert_rest(expr);

    bv_utilst::representationt rep=
      expr.op0().type().id()==ID_signedbv?bv_utilst::SIGNED:
                                          bv_utilst::UNSIGNED;

    return expr.id()==ID_overflow_minus?
      bv_utils.overflow_sub(bv0, bv1, rep):
      bv_utils.overflow_add(bv0, bv1, rep);
  }
  else if(expr.id()==ID_overflow_mult)
  {
    if(operands.size()!=2)
      throw "operand "+expr.id_string()+" takes two operands";

    if(operands[0].type().id()!=ID_unsignedbv &&
       operands[0].type().id()!=ID_signedbv)
      return SUB::convert_rest(expr);

    bvt bv0, bv1;

    convert_bv(operands[0], bv0);
    convert_bv(operands[1], bv1);

    if(bv0.size()!=bv1.size())
      throw "operand size mismatch on overflow-*";

    bv_utilst::representationt rep=
      operands[0].type().id()==ID_signedbv?bv_utilst::SIGNED:
                                           bv_utilst::UNSIGNED;

    if(operands[0].type()!=operands[1].type())
      throw "operand type mismatch on overflow-*";

    assert(bv0.size()==bv1.size());
    unsigned old_size=bv0.size();
    unsigned new_size=old_size*2;

    // sign/zero extension
    bv0=bv_utils.extension(bv0, new_size, rep);
    bv1=bv_utils.extension(bv1, new_size, rep);

    bvt result=bv_utils.multiplier(bv0, bv1, rep);

    if(rep==bv_utilst::UNSIGNED)
    {
      bvt bv_overflow;
      bv_overflow.reserve(old_size);

      // get top result bits
      for(unsigned i=old_size; i<result.size(); i++)
        bv_overflow.push_back(result[i]);

      return prop.lor(bv_overflow);
    }
    else
    {
      bvt bv_overflow;
      bv_overflow.reserve(old_size);

      // get top result bits, plus one more
      assert(old_size!=0);
      for(unsigned i=old_size-1; i<result.size(); i++)
        bv_overflow.push_back(result[i]);

      // these need to be either all 1's or all 0's
      literalt all_one=prop.land(bv_overflow);
      literalt all_zero=prop.lnot(prop.lor(bv_overflow));
      return prop.lnot(prop.lor(all_one, all_zero));
    }
  }
  else if(expr.id()==ID_overflow_unary_minus)
  {
    if(operands.size()!=1)
      throw "operand "+expr.id_string()+" takes one operand";

    bvt bv;

    convert_bv(operands[0], bv);
      
    return bv_utils.overflow_negate(bv);
  }
  else if(has_prefix(expr.id_string(), "overflow-typecast-"))
  {
    unsigned bits=atoi(expr.id().c_str()+18);

    const exprt::operandst &operands=expr.operands();

    if(operands.size()!=1)
      throw "operand "+expr.id_string()+" takes one operand";
      
    const exprt &op=operands[0];

    bvt bv;

    convert_bv(op, bv);

    if(bits>=bv.size() || bits==0)
      throw "overflow-typecast got wrong number of bits";
      
    // signed or unsigned?
    if(op.type().id()==ID_signedbv)
    {
      bvt tmp_bv;
      for(unsigned i=bits; i<bv.size(); i++)
        tmp_bv.push_back(prop.lxor(bv[bits-1], bv[i]));

      return prop.lor(tmp_bv);
    }
    else
    {
      bvt tmp_bv;
      for(unsigned i=bits; i<bv.size(); i++)
        tmp_bv.push_back(bv[i]);

      return prop.lor(tmp_bv);
    }
  }

  return SUB::convert_rest(expr);
}
