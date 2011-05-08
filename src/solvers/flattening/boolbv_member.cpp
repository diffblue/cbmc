/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <base_type.h>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_member(const member_exprt &expr, bvt &bv)
{
  bvt struct_bv;
  const exprt &struct_op=expr.struct_op();
  const typet &struct_op_type=ns.follow(struct_op.type());

  convert_bv(struct_op, struct_bv);

  if(struct_op_type.id()=="union")
  {
    unsigned width=boolbv_width(expr.type());

    if(width==0)
      return conversion_failed(expr, bv);

    bv.resize(width);

    if(width>struct_bv.size())
      throw "member/union: unexpected widths";

    for(unsigned i=0; i<width; i++)
      bv[i]=struct_bv[i];

    return;
  }

  if(struct_op_type.id()!="struct")
    throw "member takes struct or union operand";

  const irep_idt &component_name=expr.get_component_name();
  const struct_typet::componentst &components=
    to_struct_type(struct_op_type).components();

  unsigned offset=0;

  for(struct_typet::componentst::const_iterator
      it=components.begin();
      it!=components.end();
      it++)
  {
    const typet &subtype=it->type();
    unsigned sub_width=boolbv_width(subtype);

    if(it->get_name()==component_name)
    {
      if(!base_type_eq(subtype, expr.type(), ns))
      {
        #if 0
        std::cout << "DEBUG " << expr.pretty() << "\n";
        #endif

        throw "member: component type does not match: "+
          subtype.to_string()+" vs. "+
          expr.type().to_string();
      }

      bv.resize(sub_width);
      assert(offset+sub_width<=struct_bv.size());

      for(unsigned i=0; i<sub_width; i++)
        bv[i]=struct_bv[offset+i];

      return;
    }

    offset+=sub_width;
  }

  throw "component "+id2string(component_name)+" not found in structure";
}
