/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

bvt boolbvt::convert_member(const member_exprt &expr)
{
  const exprt &struct_op=expr.struct_op();
  const typet &struct_op_type=ns.follow(struct_op.type());

  const bvt &struct_bv=convert_bv(struct_op);

  const irep_idt &component_name = expr.get_component_name();
  const struct_union_typet::componentst &components =
    to_struct_union_type(struct_op_type).components();

  std::size_t offset = 0;

  for(const auto &c : components)
  {
    const typet &subtype = c.type();
    const std::size_t sub_width = boolbv_width(subtype);

    if(c.get_name() == component_name)
    {
      DATA_INVARIANT_WITH_DIAGNOSTICS(
        subtype == expr.type(),
        "component type shall match the member expression type",
        subtype.pretty(),
        expr.type().pretty());
      INVARIANT(
        offset + sub_width <= struct_bv.size(),
        "bitvector part corresponding to element shall be contained within the "
        "full aggregate bitvector");

      return bvt(
        struct_bv.begin() + offset, struct_bv.begin() + offset + sub_width);
    }

    if(struct_op_type.id() != ID_union)
      offset += sub_width;
  }

  INVARIANT_WITH_DIAGNOSTICS(
    false,
    "struct type shall contain component accessed by member expression",
    expr.find_source_location(),
    id2string(component_name));
}
