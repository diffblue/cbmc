/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_cond

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_cond(const exprt &expr, bvt &bv)
{
  const exprt::operandst &operands=expr.operands();

  unsigned width=boolbv_width(expr.type());
  
  if(width==0)
    return conversion_failed(expr, bv);

  bv.resize(width);

  // make it free variables
  Forall_literals(it, bv)
    *it=prop.new_variable();

  if(operands.size()<2)
    throw "cond takes at least two operands";

  if((operands.size()%2)!=0)
    throw "number of cond operands must be even";

  if(prop.has_set_to())
  {
    bool condition=true;
    literalt previous_cond=const_literal(false);
    literalt cond_literal=const_literal(false);

    forall_operands(it, expr)
    {
      if(condition)
      {
        cond_literal=convert(*it);
        cond_literal=prop.land(prop.lnot(previous_cond), cond_literal);

        previous_cond=prop.lor(previous_cond, cond_literal);
      }
      else
      {
        const bvt &op=convert_bv(*it);

        if(bv.size()!=op.size())
        {
          std::cerr << "result size: " << bv.size()
                    << std::endl
                    << "operand: " << op.size() << std::endl
                    << it->pretty()
                    << std::endl;

          throw "size of value operand does not match";
        }

        literalt value_literal=bv_utils.equal(bv, op);

        prop.l_set_to_true(prop.limplies(cond_literal, value_literal));
      }

      condition=!condition;
    }
  }
  else
  {
    // functional version -- go backwards
    for(unsigned i=expr.operands().size(); i!=0; i-=2)
    {
      assert(i>=2);
      const exprt &cond=expr.operands()[i-2];
      const exprt &value=expr.operands()[i-1];

      literalt cond_literal=convert(cond);

      const bvt &op=convert_bv(value);

      if(bv.size()!=op.size())
        throw "unexpected operand size in convert_cond";

      for(unsigned i=0; i<bv.size(); i++)
        bv[i]=prop.lselect(cond_literal, op[i], bv[i]);
    }
  }
}
