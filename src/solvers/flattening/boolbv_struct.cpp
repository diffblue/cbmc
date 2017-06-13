/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/base_type.h>

#include "boolbv.h"

bvt boolbvt::convert_struct(const struct_exprt &expr)
{
  const struct_typet &struct_type=to_struct_type(ns.follow(expr.type()));

  std::size_t width=boolbv_width(struct_type);

  const struct_typet::componentst &components=struct_type.components();

  if(expr.operands().size()!=components.size())
  {
    error().source_location=expr.find_source_location();
    error() << "struct: wrong number of arguments" << eom;
    throw 0;
  }

  bvt bv;
  bv.resize(width);

  std::size_t offset=0;

  exprt::operandst::const_iterator op_it=expr.operands().begin();
  for(const auto &comp : components)
  {
    const typet &subtype=comp.type();
    const exprt &op=*op_it;

    if(!base_type_eq(subtype, op.type(), ns))
    {
      error().source_location=expr.find_source_location();
      error() << "struct: component type does not match: "
              << subtype.pretty() << " vs. "
              << op.type().pretty() << eom;
      throw 0;
    }

    std::size_t subtype_width=boolbv_width(subtype);

    if(subtype_width!=0)
    {
      const bvt &op_bv=convert_bv(op);

      assert(offset<width);
      assert(op_bv.size()==subtype_width);
      assert(offset+op_bv.size()<=width);

      for(std::size_t j=0; j<op_bv.size(); j++)
        bv[offset+j]=op_bv[j];

      offset+=op_bv.size();
    }

    ++op_it;
  }

  assert(offset==width);

  return bv;
}
