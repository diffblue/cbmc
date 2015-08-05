/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

/*******************************************************************\

Function: do_reduction_op

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static literalt do_reduction_op(
  propt &prop,
  const irep_idt &id,
  const bvt &src)
{
  enum { O_OR, O_AND, O_XOR } op;

  if(id==ID_reduction_or || id==ID_reduction_nor)
    op=O_OR;
  else if(id==ID_reduction_and || id==ID_reduction_nand)
    op=O_AND;
  else if(id==ID_reduction_xor || id==ID_reduction_xnor)
    op=O_XOR;
  else
    throw "unexpected reduction operator";

  literalt l=src[0];

  for(unsigned i=1; i<src.size(); i++)
  {
    switch(op)
    {
    case O_OR:  l=prop.lor (l, src[i]); break;
    case O_AND: l=prop.land(l, src[i]); break;
    case O_XOR: l=prop.lxor(l, src[i]); break;
    }
  }

  if(id==ID_reduction_nor ||
     id==ID_reduction_nand ||
     id==ID_reduction_xnor)
    l=prop.lnot(l);
  
  return l; 
}

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

  const typet &op_type=expr.op0().type();

  if(op_type.id()==ID_verilog_signedbv ||
     op_type.id()==ID_verilog_unsignedbv)
  {
    // the reduction operators return 'x' if there is 'x' or 'z'
    bvt normal_bits=bv_utils.verilog_bv_normal_bits(bv0);
    return do_reduction_op(prop, expr.id(), normal_bits);
  }
  else
    return do_reduction_op(prop, expr.id(), bv0);
}
