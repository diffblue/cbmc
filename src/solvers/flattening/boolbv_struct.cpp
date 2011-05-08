/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <arith_tools.h>
#include <base_type.h>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_struct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_struct(const exprt &expr, bvt &bv)
{
  const struct_typet &struct_type=to_struct_type(ns.follow(expr.type()));

  unsigned width=boolbv_width(struct_type);
  
  if(width==0)
    return conversion_failed(expr, bv);

  const struct_typet::componentst &components=struct_type.components();

  if(expr.operands().size()!=components.size())
    throw "struct: wrong number of arguments";

  bv.resize(width);

  unsigned offset=0, i=0;

  for(struct_typet::componentst::const_iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    const typet &subtype=it->type();
    const exprt &op=expr.operands()[i];

    if(!base_type_eq(subtype, op.type(), ns))
      throw "struct: component type does not match: "+
        subtype.to_string()+" vs. "+
        op.type().to_string();
        
    unsigned subtype_width=boolbv_width(subtype);

    if(subtype_width!=0)
    {
      bvt op_bv;
      
      convert_bv(op, op_bv);
    
      assert(offset<width);
      assert(op_bv.size()==subtype_width);
      assert(offset+op_bv.size()<=width);

      for(unsigned j=0; j<op_bv.size(); j++)
        bv[offset+j]=op_bv[j];

      offset+=op_bv.size();
    }

    i++;    
  }
  
  assert(offset==width);
}
