/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/config.h>

#include "bv_endianness_map.h"

static bvt convert_member_struct(
  const member_exprt &expr,
  const bvt &struct_bv,
  const boolbv_widtht &boolbv_width,
  const namespacet &ns)
{
  const exprt &struct_op=expr.struct_op();
  const typet &struct_op_type=ns.follow(struct_op.type());

  const irep_idt &component_name = expr.get_component_name();
  const struct_typet::componentst &components =
    to_struct_type(struct_op_type).components();

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

    offset += sub_width;
  }

  INVARIANT_WITH_DIAGNOSTICS(
    false,
    "struct type shall contain component accessed by member expression",
    expr.find_source_location(),
    id2string(component_name));
}

static bvt convert_member_union(
  const member_exprt &expr,
  const bvt &union_bv,
  const boolbv_widtht &boolbv_width,
  const namespacet &ns)
{
  const exprt &union_op = expr.compound();
  const union_typet &union_op_type =
    ns.follow_tag(to_union_tag_type(union_op.type()));

  const irep_idt &component_name = expr.get_component_name();
  const union_typet::componentt &component =
    union_op_type.get_component(component_name);
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    component.is_not_nil(),
    "union type shall contain component accessed by member expression",
    expr.find_source_location(),
    id2string(component_name));

  const typet &subtype = component.type();
  const std::size_t sub_width = boolbv_width(subtype);

  if(
    config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN)
  {
    return bvt(union_bv.begin(), union_bv.begin() + sub_width);
  }
  else
  {
    DATA_INVARIANT(
      config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_BIG_ENDIAN,
      "endianness should be configured to little or big endian");

    bv_endianness_mapt map_u(union_op_type, false, ns, boolbv_width);
    bv_endianness_mapt map_component(subtype, false, ns, boolbv_width);

    bvt result(sub_width, literalt{});
    for(std::size_t i = 0; i < sub_width; ++i)
      result[map_u.map_bit(i)] = union_bv[map_component.map_bit(i)];

    return result;
  }
}

bvt boolbvt::convert_member(const member_exprt &expr)
{
  const bvt &compound_bv = convert_bv(expr.compound());

  if(expr.compound().type().id() == ID_struct_tag)
    return convert_member_struct(expr, compound_bv, boolbv_width, ns);
  else
  {
    PRECONDITION(expr.compound().type().id() == ID_union_tag);
    return convert_member_union(expr, compound_bv, boolbv_width, ns);
  }
}
