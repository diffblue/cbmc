/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/namespace.h>

bvt boolbvt::convert_struct(const struct_exprt &expr)
{
  const struct_typet &struct_type=to_struct_type(ns.follow(expr.type()));

  std::size_t width=boolbv_width(struct_type);

  const struct_typet::componentst &components=struct_type.components();

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    expr.operands().size() == components.size(),
    "number of operands of a struct expression shall equal the number of"
    "components as indicated by its type",
    expr.find_source_location());

  bvt bv;
  bv.resize(width);

  std::size_t bit_idx = 0;

  exprt::operandst::const_iterator op_it=expr.operands().begin();
  for(const auto &comp : components)
  {
    const typet &subtype=comp.type();
    const exprt &op=*op_it;

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      subtype == op.type(),
      "type of a struct expression operand shall equal the type of the "
      "corresponding struct component",
      expr.find_source_location(),
      subtype.pretty(),
      op.type().pretty());

    std::size_t subtype_width=boolbv_width(subtype);

    if(subtype_width!=0)
    {
      const bvt &op_bv = convert_bv(op, subtype_width);

      INVARIANT(
        bit_idx + op_bv.size() <= width, "bit index shall be within bounds");

      for(const auto &bit : op_bv)
      {
        bv[bit_idx] = bit;
        bit_idx++;
      }
    }

    ++op_it;
  }

  INVARIANT(
    bit_idx == width, "all bits in the bitvector shall have been assigned");

  return bv;
}
