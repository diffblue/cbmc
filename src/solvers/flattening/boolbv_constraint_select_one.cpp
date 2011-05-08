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

  if(expr.id()!="constraint_select_one")
    throw "expected constraint_select_one expression";

  if(operands.size()<2)
    throw "constraint_select_one takes at least two operands";

  if(expr.type()!=expr.op0().type())
    throw "constraint_select_one expects matching types";
    
  if(prop.has_set_to())
  {
    std::vector<bvt> op_bv;
    op_bv.resize(expr.operands().size());

    unsigned i=0;
    forall_operands(it, expr)
      convert_bv(*it, op_bv[i++]);

    bv=op_bv[0];

    // add constraints

    bvt equal_bv;
    equal_bv.resize(bv.size());

    bvt b;
    b.reserve(op_bv.size()-1);

    for(unsigned i=1; i<op_bv.size(); i++)
    {
      if(op_bv[i].size()!=bv.size())
        throw "constraint_select_one expects matching width";

      for(unsigned j=0; j<bv.size(); j++)
        equal_bv[j]=prop.lequal(bv[j], op_bv[i][j]);

      b.push_back(prop.land(equal_bv));
    }

    prop.l_set_to_true(prop.lor(b));
  }
  else
  {
    unsigned op_nr=0;
    forall_operands(it, expr)
    {
      bvt op_bv;
      convert_bv(*it, op_bv);

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

