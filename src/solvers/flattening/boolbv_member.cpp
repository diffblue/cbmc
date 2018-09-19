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
  else if(struct_op_type.id()==ID_struct)
  {
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
        if(!base_type_eq(subtype, expr.type(), ns))
        {
          #if 0
          std::cout << "DEBUG " << expr.pretty() << "\n";
          #endif

          error().source_location=expr.find_source_location();
          error() << "member: component type does not match: "
                  << subtype.pretty() << " vs. "
                  << expr.type().pretty() << eom;
          throw 0;
        }

        bvt bv;
        bv.resize(sub_width);
        assert(offset+sub_width<=struct_bv.size());

        for(std::size_t i=0; i<sub_width; i++)
          bv[i]=struct_bv[offset+i];

        return bv;
      }

      offset+=sub_width;
    }

    error().source_location=expr.find_source_location();
    error() << "component " << component_name
            << " not found in structure" << eom;
    throw 0;
  }
  else
  {
    error().source_location=expr.find_source_location();
    error() << "member takes struct or union operand" << eom;
    throw 0;
  }
}
