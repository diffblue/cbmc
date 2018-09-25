/*******************************************************************\

Module: Bit-blasting of bswap

Author: Michael Tautschnig

\*******************************************************************/

#include "boolbv.h"

#include <util/invariant.h>

bvt boolbvt::convert_bswap(const bswap_exprt &expr)
{
  const std::size_t width = boolbv_width(expr.type());

  // width must be multiple of bytes
  const std::size_t byte_bits = expr.get_bits_per_byte();
  if(width % byte_bits != 0)
    return conversion_failed(expr);

  bvt result = convert_bv(expr.op(), width);

  std::size_t dest_base = width;

  for(std::size_t src = 0; src < width; ++src)
  {
    std::size_t bit_offset = src % byte_bits;
    if(bit_offset == 0)
      dest_base -= byte_bits;

    if(src >= dest_base)
      break;

    result[src].swap(result[dest_base + bit_offset]);
  }

  return result;
}
