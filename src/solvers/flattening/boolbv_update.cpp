/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/namespace.h>

bvt boolbvt::convert_update(const update_exprt &expr)
{
  const exprt::operandst &ops=expr.operands();

  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  bvt bv=convert_bv(ops[0]);

  if(bv.size()!=width)
    throw "update: unexpected operand 0 width";

  // start the recursion
  convert_update_rec(
    expr.op1().operands(), 0, expr.type(), 0, expr.op2(), bv);

  return bv;
}

void boolbvt::convert_update_rec(
  const exprt::operandst &designators,
  std::size_t d,
  const typet &type,
  std::size_t offset,
  const exprt &new_value,
  bvt &bv)
{
  if(d>=designators.size())
  {
    // done
    bvt new_value_bv=convert_bv(new_value);
    std::size_t new_value_width=boolbv_width(type);

    if(new_value_width!=new_value_bv.size())
      throw "convert_update_rec: unexpected new_value size";

    // update
    for(std::size_t i=0; i<new_value_width; i++)
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

    bvt index_bv = convert_bv(to_index_designator(designator).index());

    const array_typet &array_type=to_array_type(type);
    const typet &subtype = array_type.element_type();
    const exprt &size_expr = array_type.size();

    std::size_t element_size=boolbv_width(subtype);

    DATA_INVARIANT(
      size_expr.id() == ID_constant,
      "array in update expression should be constant-sized");

    // iterate over array
    const std::size_t size =
      numeric_cast_v<std::size_t>(to_constant_expr(size_expr));

    bvt tmp_bv=bv;

    for(std::size_t i = 0; i != size; ++i)
    {
      std::size_t new_offset=offset+i*element_size;

      convert_update_rec(
        designators, d+1, subtype, new_offset, new_value, tmp_bv);

      bvt const_bv=bv_utils.build_constant(i, index_bv.size());
      literalt equal=bv_utils.equal(const_bv, index_bv);

      for(std::size_t j=0; j<element_size; j++)
      {
        std::size_t idx=new_offset+j;
        assert(idx<bv.size());
        bv[idx]=prop.lselect(equal, tmp_bv[idx], bv[idx]);
      }
    }
  }
  else if(designator.id()==ID_member_designator)
  {
    const irep_idt &component_name=designator.get(ID_component_name);

    if(ns.follow(type).id() == ID_struct)
    {
      const struct_typet &struct_type = to_struct_type(ns.follow(type));

      std::size_t struct_offset=0;

      struct_typet::componentt component;
      component.make_nil();

      const struct_typet::componentst &components=
        struct_type.components();

      for(const auto &c : components)
      {
        const typet &subtype = c.type();
        std::size_t sub_width=boolbv_width(subtype);

        if(c.get_name() == component_name)
        {
          component = c;
          break; // done
        }

        struct_offset+=sub_width;
      }

      if(component.is_nil())
        throw "update: failed to find struct component";

      const typet &new_type = component.type();

      std::size_t new_offset=offset+struct_offset;

      // recursive call
      convert_update_rec(
        designators, d+1, new_type, new_offset, new_value, bv);
    }
    else if(ns.follow(type).id() == ID_union)
    {
      const union_typet &union_type = to_union_type(ns.follow(type));

      const union_typet::componentt &component=
        union_type.get_component(component_name);

      if(component.is_nil())
        throw "update: failed to find union component";

      // this only adjusts the type, the offset stays as-is

      const typet &new_type = component.type();

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
