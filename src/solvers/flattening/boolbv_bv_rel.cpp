/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <std_types.h>

#include "boolbv.h"
#include "boolbv_type.h"

#ifdef HAVE_FLOATBV
#include "../floatbv/float_utils.h"
#endif

/*******************************************************************\

Function: boolbvt::convert_bv_rel

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolbvt::convert_bv_rel(const exprt &expr)
{
  const exprt::operandst &operands=expr.operands();
  const std::string &rel=expr.id_string();

  if(operands.size()==2)
  {
    const exprt &op0=expr.op0();
    const exprt &op1=expr.op1();

    bvt bv0, bv1;

    convert_bv(op0, bv0);
    convert_bv(op1, bv1);

    bvtypet bvtype0=get_bvtype(op0.type());
    bvtypet bvtype1=get_bvtype(op1.type());

    if(bv0.size()==bv1.size() && bv0.size()!=0 &&
       bvtype0==bvtype1)
    {
      if(bvtype0==IS_FLOAT)
      {
        #ifdef HAVE_FLOATBV
        float_utilst float_utils(prop);
        float_utils.spec=to_floatbv_type(op0.type());

        if(rel=="<=")
          return float_utils.relation(bv0, float_utilst::LE, bv1);
        else if(rel=="<")
          return float_utils.relation(bv0, float_utilst::LT, bv1);
        else if(rel==">=")
          return float_utils.relation(bv0, float_utilst::GE, bv1);
        else if(rel==">")
          return float_utils.relation(bv0, float_utilst::GT, bv1);
        else
          return SUB::convert_rest(expr);
        #else
        return SUB::convert_rest(expr);
        #endif
      }
      else if((op0.type().id()=="range" &&
               op1.type()==op0.type()) ||
               bvtype0==IS_SIGNED ||
               bvtype0==IS_UNSIGNED ||
               bvtype0==IS_FIXED)
      {
        literalt literal;
        bool or_equal=(rel=="<=" || rel==">=");

        bv_utilst::representationt rep=
          ((bvtype0==IS_SIGNED) || (bvtype0==IS_FIXED))?bv_utilst::SIGNED:
                                                        bv_utilst::UNSIGNED;

        if(rel=="<=" || rel=="<")
          literal=bv_utils.lt_or_le(or_equal, bv0, bv1, rep);
        else if(rel==">=" || rel==">")
          literal=bv_utils.lt_or_le(or_equal, bv1, bv0, rep);
                                              // swapped
        else
          return SUB::convert_rest(expr);

        if(prop.has_set_to())
        {
          // it's unclear if this helps
          if(bv0.size()>8)
          {
            literalt equal_lit=equality(op0, op1);

            if(or_equal)
              prop.l_set_to_true(prop.limplies(equal_lit, literal));
            else
              prop.l_set_to_true(prop.limplies(equal_lit, prop.lnot(literal)));
          }          
        }
 
        return literal;
      }
    }
  }

  return SUB::convert_rest(expr);
}

