/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>
#include <util/config.h>

#include "bv_endianness_map.h"

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

  if(config.ansi_c.endianness==configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN)
  {
    for(std::size_t i=0; i<op_bv.size(); i++)
      bv[i]=op_bv[i];

    // pad with nondets
    for(std::size_t i=op_bv.size(); i<bv.size(); i++)
      bv[i]=prop.new_variable();
  }
  else
  {
    INVARIANT(
      config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_BIG_ENDIAN,
      "endianness should be set to either little endian or big endian");

    bv_endianness_mapt map_u(expr.type(), false, ns, boolbv_width);
    bv_endianness_mapt map_op(expr.op0().type(), false, ns, boolbv_width);

    for(std::size_t i=0; i<op_bv.size(); i++)
      bv[map_u.map_bit(i)]=op_bv[map_op.map_bit(i)];

    // pad with nondets
    for(std::size_t i=op_bv.size(); i<bv.size(); i++)
      bv[map_u.map_bit(i)]=prop.new_variable();
  }

  return bv;
}
