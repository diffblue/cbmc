/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <arith_tools.h>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_union(const exprt &expr, bvt &bv)
{
  unsigned width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr, bv);

  if(expr.operands().size()!=1)
    throw "union expects one argument";

  bvt op_bv;
  convert_bv(expr.op0(), op_bv);

  if(width<op_bv.size())
    throw "union: unexpected operand op width";

  bv.resize(width);
  
  for(unsigned i=0; i<op_bv.size(); i++)
    bv[i]=op_bv[i];

  // pad with nondets
  for(unsigned i=op_bv.size(); i<bv.size(); i++)
    bv[i]=prop.new_variable();

  const irep_idt &component_name=expr.get("component_name");
  const irept &components=expr.type().find("components");

  const union_typet &union_type=to_union_type(expr.type());

  if(!union_type.has_component(component_name))
    throw "union: component not found";

  unsigned number=union_type.component_number(component_name);

  unsigned component_bits=
    integer2long(address_bits(components.get_sub().size()));

  unsigned offset=width-component_bits;

  for(unsigned i=0; i<component_bits; i++)
    bv[offset+i]=const_literal((number>>i)&1);
}
