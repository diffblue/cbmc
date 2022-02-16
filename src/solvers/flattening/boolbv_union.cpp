/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

bvt boolbvt::convert_union(const union_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  const bvt &op_bv=convert_bv(expr.op());

  INVARIANT(
    op_bv.size() <= width,
    "operand bitvector width shall not be larger than the width indicated by "
    "the union type");

  bvt bv;
  bv.resize(width);

  endianness_mapt map_u = endianness_map(expr.type());
  endianness_mapt map_op = endianness_map(expr.op().type());

  for(std::size_t i = 0; i < op_bv.size(); i++)
    bv[map_u.map_bit(i)] = op_bv[map_op.map_bit(i)];

  // pad with nondets
  for(std::size_t i = op_bv.size(); i < bv.size(); i++)
    bv[map_u.map_bit(i)] = prop.new_variable();

  return bv;
}

bvt boolbvt::convert_empty_union(const empty_union_exprt &expr)
{
  return {};
}
