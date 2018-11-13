/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/std_types.h>

#include "boolbv_type.h"

#include <solvers/floatbv/float_utils.h>

/// Flatten <, >, <= and >= expressions.
literalt boolbvt::convert_bv_rel(const exprt &expr)
{
  const exprt::operandst &operands=expr.operands();
  const irep_idt &rel=expr.id();

  if(operands.size()==2)
  {
    const exprt &op0=expr.op0();
    const exprt &op1=expr.op1();

    const bvt &bv0=convert_bv(op0);
    const bvt &bv1=convert_bv(op1);

    bvtypet bvtype0=get_bvtype(op0.type());
    bvtypet bvtype1=get_bvtype(op1.type());

    if(bv0.size()==bv1.size() && !bv0.empty() &&
       bvtype0==bvtype1)
    {
      if(bvtype0==bvtypet::IS_FLOAT)
      {
        float_utilst float_utils(prop, to_floatbv_type(op0.type()));

        if(rel==ID_le)
          return float_utils.relation(bv0, float_utilst::relt::LE, bv1);
        else if(rel==ID_lt)
          return float_utils.relation(bv0, float_utilst::relt::LT, bv1);
        else if(rel==ID_ge)
          return float_utils.relation(bv0, float_utilst::relt::GE, bv1);
        else if(rel==ID_gt)
          return float_utils.relation(bv0, float_utilst::relt::GT, bv1);
        else
          return SUB::convert_rest(expr);
      }
      else if((op0.type().id()==ID_range &&
               op1.type()==op0.type()) ||
               bvtype0==bvtypet::IS_SIGNED ||
               bvtype0==bvtypet::IS_UNSIGNED ||
               bvtype0==bvtypet::IS_FIXED)
      {
        literalt literal;

        bv_utilst::representationt rep=
          ((bvtype0==bvtypet::IS_SIGNED) || (bvtype0==bvtypet::IS_FIXED))?
             bv_utilst::representationt::SIGNED:
             bv_utilst::representationt::UNSIGNED;

        #if 1

        return bv_utils.rel(bv0, expr.id(), bv1, rep);

        #else
        literalt literal=bv_utils.rel(bv0, expr.id(), bv1, rep);

        if(prop.has_set_to())
        {
          // it's unclear if this helps
          if(bv0.size()>8)
          {
            literalt equal_lit=equality(op0, op1);

            if(or_equal)
              prop.l_set_to_true(prop.limplies(equal_lit, literal));
            else
              prop.l_set_to_true(prop.limplies(equal_lit, !literal));
          }
        }

        return literal;
        #endif
      }
      else if((bvtype0==bvtypet::IS_VERILOG_SIGNED ||
               bvtype0==bvtypet::IS_VERILOG_UNSIGNED) &&
              op0.type()==op1.type())
      {
        // extract number bits
        bvt extract0, extract1;

        extract0.resize(bv0.size()/2);
        extract1.resize(bv1.size()/2);

        for(std::size_t i=0; i<extract0.size(); i++)
          extract0[i]=bv0[i*2];

        for(std::size_t i=0; i<extract1.size(); i++)
          extract1[i]=bv1[i*2];

        bv_utilst::representationt rep=bv_utilst::representationt::UNSIGNED;

        // now compare
        return bv_utils.rel(extract0, expr.id(), extract1, rep);
      }
    }
  }

  return SUB::convert_rest(expr);
}
