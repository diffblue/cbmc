/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/base_type.h>
#include <util/byte_operators.h>
#include <util/arith_tools.h>
#include <util/c_types.h>

bvt boolbvt::convert_member(const member_exprt &expr)
{
  const exprt &struct_op=expr.struct_op();
  const typet &struct_op_type=ns.follow(struct_op.type());

  const bvt &struct_bv=convert_bv(struct_op);

  if(struct_op_type.id()==ID_union)
  {
    return convert_bv(
      byte_extract_exprt(byte_extract_id(),
                         struct_op,
                         from_integer(0, index_type()),
                         expr.type()));
  }
  else
  {
    INVARIANT(
      struct_op_type.id() == ID_struct,
      "member_exprt should denote access to a union or struct");

    const irep_idt &component_name=expr.get_component_name();
    const struct_typet::componentst &components=
      to_struct_type(struct_op_type).components();

    std::size_t offset=0;

    for(const auto &c : components)
    {
      const typet &subtype = c.type();
      std::size_t sub_width=boolbv_width(subtype);

      if(c.get_name() == component_name)
      {
        DATA_INVARIANT_WITH_DIAGNOSTICS(
          base_type_eq(subtype, expr.type(), ns),
          "struct component type shall match the member expression type",
          subtype.pretty(),
          expr.type().pretty());

        bvt bv;
        bv.resize(sub_width);
        INVARIANT(
          offset + sub_width <= struct_bv.size(),
          "bitvector part corresponding to struct element shall be contained "
          "within the full struct bitvector");

        for(std::size_t i=0; i<sub_width; i++)
          bv[i]=struct_bv[offset+i];

        return bv;
      }

      offset+=sub_width;
    }

    INVARIANT_WITH_DIAGNOSTICS(
      false,
      "struct type shall contain component accessed by member expression",
      expr.find_source_location(),
      id2string(component_name));
  }
}
