/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/base_type.h>
#include <util/config.h>
#include <util/expr_util.h>
#include <util/pointer_offset_size.h>

#include <ansi-c/c_types.h>

#include "boolbv.h"

/*******************************************************************\

Function: boolbvt::convert_update

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_update(const exprt &expr, bvt &bv)
{
  const exprt::operandst &ops=expr.operands();

  if(ops.size()!=3)
    throw "update takes at three operands";

  unsigned width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr, bv);

  bv=convert_bv(ops[0]);

  if(bv.size()!=width)
    throw "update: unexpected operand 0 width";

  // start the recursion
  convert_update_rec(
    expr.op1().operands(), 0, expr.type(), 0, expr.op2(), bv);
}

/*******************************************************************\

Function: boolbvt::convert_update_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbvt::convert_update_rec(
  const exprt::operandst &designators,
  unsigned d,
  const typet &type,
  unsigned offset,
  const exprt &new_value,
  bvt &bv)
{
  if(type.id()==ID_symbol)
    convert_update_rec(
      designators, d, ns.follow(type), offset, new_value, bv);

  if(d>=designators.size())
  {
    // done
    bvt new_value_bv=convert_bv(new_value);
    unsigned new_value_width=boolbv_width(type);
    
    if(new_value_width!=new_value_bv.size())
      throw "convert_update_rec: unexpected new_value size";

    // update
    for(unsigned i=0; i<new_value_width; i++)
    {
      assert(offset+i<bv.size());
      bv[offset+i]=new_value_bv[i];
    }
    
    return;
  }

  const exprt &designator=designators[d];

  if(designator.id()==ID_index_designator)
  {
    if(type.id()!=ID_array)
      throw "update: index designator needs array";
      
    if(designator.operands().size()!=1)
      throw "update: index designator takes one operand";
      
    bvt index_bv=convert_bv(designator.op0());

    const array_typet &array_type=to_array_type(type);
    
    const typet &subtype=ns.follow(array_type.subtype());

    unsigned element_size=boolbv_width(subtype);

    // iterate over array
    mp_integer size;
    if(to_integer(array_type.size(), size))
      throw "update: failed to get array size";
      
    bvt tmp_bv=bv;
    
    for(unsigned i=0; i!=integer2long(size); ++i)
    {
      unsigned new_offset=offset+i*element_size;
      
      convert_update_rec(
        designators, d+1, subtype, new_offset, new_value, tmp_bv);

      bvt const_bv=bv_utils.build_constant(i, index_bv.size());
      literalt equal=bv_utils.equal(const_bv, index_bv);

      for(unsigned j=0; j<element_size; j++)
      {
        unsigned idx=new_offset+j;
        assert(idx<bv.size());
        bv[idx]=prop.lselect(equal, tmp_bv[idx], bv[idx]);
      }
    }
  }
  else if(designator.id()==ID_member_designator)
  {
    const irep_idt &component_name=designator.get(ID_component_name);
  
    if(type.id()==ID_struct)
    {
      const struct_typet &struct_type=
        to_struct_type(type);

      unsigned struct_offset=0;
      
      struct_typet::componentt component;
      component.make_nil();

      const struct_typet::componentst &components=
        struct_type.components();

      for(struct_typet::componentst::const_iterator
          it=components.begin();
          it!=components.end();
          it++)
      {
        const typet &subtype=it->type();
        unsigned sub_width=boolbv_width(subtype);

        if(it->get_name()==component_name)
        {
          component=*it;
          break; // done
        }

        struct_offset+=sub_width;
      }
        
      if(component.is_nil())
        throw "update: failed to find struct component";

      const typet &new_type=ns.follow(component.type());

      unsigned new_offset=offset+struct_offset;

      // recursive call
      convert_update_rec(
        designators, d+1, new_type, new_offset, new_value, bv);
    }
    else if(type.id()==ID_union)
    {
      const union_typet &union_type=
        to_union_type(type);

      const union_typet::componentt &component=
        union_type.get_component(component_name);
        
      if(component.is_nil())
        throw "update: failed to find union component";

      // this only adjusts the type, the offset stays as-is

      const typet &new_type=ns.follow(component.type());

      // recursive call
      convert_update_rec(
        designators, d+1, new_type, offset, new_value, bv);
    }
    else
      throw "update: member designator needs struct or union";
  }
  else
    throw "update: unexpected designator";
}

