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

  // When the update value's width is not a multiple of the byte width,
  // lower_byte_update places the value at the high end of the last partial
  // byte (concatenating {value, remaining_low_bits}). For little-endian the
  // high end is at higher bit indices, so the *whole* value is shifted up by
  // byte_width - tail_bits (the low tail_shift bits of the target keep their
  // original value). For big-endian the endianness map already places bit 0
  // at the MSB, so no shift is needed.
  //
  // TODO: This MSB-first placement matches lower_byte_update, but
  // simplify_byte_update's expr2bits/bits2expr path places a sub-byte value
  // LSB-first, so the two disagree for non-byte-aligned updates (e.g. writing
  // a 1-bit 0 over 0xFFFFFFFF yields 0xFFFFFF7F here but 0xFFFFFFFE via the
  // simplifier). That is why the regression tests run with --no-simplify and
  // assert the concrete bit pattern. The canonical convention should be picked
  // and both paths aligned in a follow-up.
  const std::size_t tail_bits = update_width % byte_width;
  const std::size_t tail_shift =
    little_endian && tail_bits != 0 ? byte_width - tail_bits : 0;

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
      const std::size_t shifted_offset_i = offset_i + tail_shift;

      for(std::size_t i = 0; i < update_width; i++)
      {
        size_t index_op = map_op.map_bit(shifted_offset_i + i);
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

    const std::size_t shifted_offset = offset + tail_shift;
    for(std::size_t bit=0; bit<update_width; bit++)
      if(shifted_offset + bit < bv.size())
      {
        std::size_t bv_o = map_op.map_bit(shifted_offset + bit);
        std::size_t value_bv_o=map_value.map_bit(bit);

        bv[bv_o]=prop.lselect(equal, value_bv[value_bv_o], bv[bv_o]);
      }
  }

  return bv;
}
