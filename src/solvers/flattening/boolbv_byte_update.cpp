/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/invariant.h>

bvt boolbvt::convert_byte_update(const byte_update_exprt &expr)
{
  // if we update (from) an unbounded array, lower the expression as the array
  // logic does not handle byte operators
  if(
    is_unbounded_array(expr.op().type()) ||
    is_unbounded_array(expr.value().type()))
  {
    return convert_bv(lower_byte_update(expr, ns));
  }

  const exprt &op = expr.op();
  const exprt &offset_expr=expr.offset();
  const exprt &value=expr.value();

  PRECONDITION(
    expr.id() == ID_byte_update_little_endian ||
    expr.id() == ID_byte_update_big_endian);
  const bool little_endian = expr.id() == ID_byte_update_little_endian;

  bvt bv=convert_bv(op);

  const bvt &value_bv=convert_bv(value);
  std::size_t update_width=value_bv.size();
  std::size_t byte_width = expr.get_bits_per_byte();

  if(update_width>bv.size())
    update_width=bv.size();

  // see if the byte number is constant

  const auto index = numeric_cast<mp_integer>(offset_expr);
  if(index.has_value())
  {
    // yes!
    const mp_integer offset = *index * byte_width;

    if(offset+update_width>mp_integer(bv.size()) || offset<0)
    {
      // out of bounds
    }
    else
    {
      endianness_mapt map_op = endianness_map(op.type(), little_endian);
      endianness_mapt map_value = endianness_map(value.type(), little_endian);

      const std::size_t offset_i = numeric_cast_v<std::size_t>(offset);

      for(std::size_t i = 0; i < update_width; i++)
      {
        size_t index_op = map_op.map_bit(offset_i + i);
        size_t index_value = map_value.map_bit(i);

        INVARIANT(
          index_op < bv.size(), "bit vector index shall be within bounds");
        INVARIANT(
          index_value < value_bv.size(),
          "bit vector index shall be within bounds");

        bv[index_op] = value_bv[index_value];
      }
    }

    return bv;
  }

  // byte_update with variable index
  for(std::size_t offset=0; offset<bv.size(); offset+=byte_width)
  {
    // index condition
    equal_exprt equality(
      offset_expr, from_integer(offset / byte_width, offset_expr.type()));
    literalt equal=convert(equality);

    endianness_mapt map_op = endianness_map(op.type(), little_endian);
    endianness_mapt map_value = endianness_map(value.type(), little_endian);

    for(std::size_t bit=0; bit<update_width; bit++)
      if(offset+bit<bv.size())
      {
        std::size_t bv_o=map_op.map_bit(offset+bit);
        std::size_t value_bv_o=map_value.map_bit(bit);

        bv[bv_o]=prop.lselect(equal, value_bv[value_bv_o], bv[bv_o]);
      }
  }

  return bv;
}
