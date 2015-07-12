/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_constraint_select_one

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_constraint_select_one(const exprt &expr, bvt &bv)
{
  const exprt::operandst &operands=expr.operands();

  if(expr.id()!=ID_constraint_select_one)
    throw "expected constraint_select_one expression";

  if(operands.empty())
    throw "constraint_select_one takes at one operand";

  if(expr.type()!=expr.op0().type())
    throw "constraint_select_one expects matching types";
 
  if(prop.has_set_to())
  {
    unsigned width=boolbv_width(expr.type());
    bv=prop.new_variables(width);

    bvt b;
    b.reserve(expr.operands().size());

    // add constraints
    forall_operands(it, expr)
    {
      bvt it_bv=convert_bv(*it);

      if(it_bv.size()!=bv.size())
        throw "constraint_select_one expects matching width";

      b.push_back(bv_utils.equal(bv, it_bv));
    }

    prop.lcnf(b);
  }
  else
  {
    unsigned op_nr=0;
    forall_operands(it, expr)
    {
      const bvt &op_bv=convert_bv(*it);

      if(op_nr==0)
        bv=op_bv;
      else
      {
        if(op_bv.size()!=bv.size())
          return conversion_failed(expr, bv);

        for(unsigned i=0; i<op_bv.size(); i++)
          bv[i]=prop.lselect(prop.new_variable(), bv[i], op_bv[i]);
      }

      op_nr++;
    }
  }
}

