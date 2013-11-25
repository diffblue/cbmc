/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_reduction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolbvt::convert_reduction(const exprt &expr)
{
  if(expr.operands().size()!=1)
    throw "reduction operators take one operand";

  const bvt &bv0=convert_bv(expr.op0());

  if(bv0.size()<1)
    throw "reduction operators take one non-empty operand";

  literalt l;

  enum { O_OR, O_AND, O_XOR } op;

  if(expr.id()==ID_reduction_or || expr.id()==ID_reduction_nor)
    op=O_OR;
  else if(expr.id()==ID_reduction_and || expr.id()==ID_reduction_nand)
    op=O_AND;
  else if(expr.id()==ID_reduction_xor || expr.id()==ID_reduction_xnor)
    op=O_XOR;
  else
    throw "unexpected reduction operator";

  l=bv0[0];
  for(unsigned i=1; i<bv0.size(); i++)
  {
    switch(op)
    {
    case O_OR:  l=prop.lor (l, bv0[i]); break;
    case O_AND: l=prop.land(l, bv0[i]); break;
    case O_XOR: l=prop.lxor(l, bv0[i]); break;
    }
  }

  if(expr.id()==ID_reduction_nor ||
     expr.id()==ID_reduction_nand ||
     expr.id()==ID_reduction_xnor)
    l=prop.lnot(l);
  
  return l; 
}
