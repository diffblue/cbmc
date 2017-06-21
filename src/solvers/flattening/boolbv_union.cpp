/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include <util/arith_tools.h>
#include <util/config.h>
#include <util/endianness_map.h>

#include "boolbv.h"

bvt boolbvt::convert_union(const union_exprt &expr)
{
  std::size_t width=boolbv_width(expr.type());

  if(width==0)
    return conversion_failed(expr);

  const bvt &op_bv=convert_bv(expr.op());

  if(width<op_bv.size())
    throw "union: unexpected operand op width";

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
    assert(
      config.ansi_c.endianness==configt::ansi_ct::endiannesst::IS_BIG_ENDIAN);

    endianness_mapt map_u(expr.type(), false, ns);
    endianness_mapt map_op(expr.op0().type(), false, ns);

    for(std::size_t i=0; i<op_bv.size(); i++)
      bv[map_u.map_bit(i)]=op_bv[map_op.map_bit(i)];

    // pad with nondets
    for(std::size_t i=op_bv.size(); i<bv.size(); i++)
      bv[map_u.map_bit(i)]=prop.new_variable();
  }

  return bv;
}
