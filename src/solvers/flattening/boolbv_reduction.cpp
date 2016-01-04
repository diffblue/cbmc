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

literalt boolbvt::convert_reduction(const unary_exprt &expr)
{
  const bvt &op_bv=convert_bv(expr.op());

  if(op_bv.size()<1)
    throw "reduction operators take one non-empty operand";

  enum { O_OR, O_AND, O_XOR } op;
  
  const irep_idt id=expr.id();

  if(id==ID_reduction_or || id==ID_reduction_nor)
    op=O_OR;
  else if(id==ID_reduction_and || id==ID_reduction_nand)
    op=O_AND;
  else if(id==ID_reduction_xor || id==ID_reduction_xnor)
    op=O_XOR;
  else
    throw "unexpected reduction operator";

  literalt l=op_bv[0];

  for(unsigned i=1; i<op_bv.size(); i++)
  {
    switch(op)
    {
    case O_OR:  l=prop.lor (l, op_bv[i]); break;
    case O_AND: l=prop.land(l, op_bv[i]); break;
    case O_XOR: l=prop.lxor(l, op_bv[i]); break;
    }
  }

  if(id==ID_reduction_nor ||
     id==ID_reduction_nand ||
     id==ID_reduction_xnor)
    l=!l;
  
  return l; 
}

/*******************************************************************\

Function: boolbvt::convert_reduction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_reduction(const unary_exprt &expr, bvt &bv)
{
  const bvt &op_bv=convert_bv(expr.op());

  if(op_bv.size()<1)
    throw "reduction operators take one non-empty operand";

  enum { O_OR, O_AND, O_XOR } op;
  
  const irep_idt id=expr.id();

  if(id==ID_reduction_or || id==ID_reduction_nor)
    op=O_OR;
  else if(id==ID_reduction_and || id==ID_reduction_nand)
    op=O_AND;
  else if(id==ID_reduction_xor || id==ID_reduction_xnor)
    op=O_XOR;
  else
    throw "unexpected reduction operator";

  const typet &op_type=expr.op().type();

  if(op_type.id()!=ID_verilog_signedbv ||
     op_type.id()!=ID_verilog_unsignedbv)
  {
    if((expr.type().id()==ID_verilog_signedbv ||
        expr.type().id()==ID_verilog_unsignedbv) &&
        expr.type().get_int(ID_width)==1)
    {
      bv.resize(2);
      
      literalt l0=op_bv[0], l1=op_bv[1];

      for(unsigned i=2; i<op_bv.size(); i+=2)
      {
        switch(op)
        {
        case O_OR:  l0=prop.lor (l0, op_bv[i]); l1=prop.lor(l1, op_bv[i+1]); break;
        case O_AND: l0=prop.land(l0, op_bv[i]); l1=prop.lor(l1, op_bv[i+1]); break;
        case O_XOR: l0=prop.lxor(l0, op_bv[i]); l1=prop.lor(l1, op_bv[i+1]); break;
        }
      }
      
      // Dominating values?
      if(op==O_OR)
        l1=prop.lselect(l0, const_literal(false), l1);
      else if(op==O_AND)
        l1=prop.lselect(l0, l1, const_literal(false));

      if(id==ID_reduction_nor ||
         id==ID_reduction_nand ||
         id==ID_reduction_xnor)
        l0=!l0;

      // we give back 'x', which is 10, if we had seen a 'z'
      l0=prop.lselect(l1, const_literal(false), l0);
      
      bv[0]=l0;
      bv[1]=l1;

      return;
    }
  }


  return conversion_failed(expr, bv);
}
