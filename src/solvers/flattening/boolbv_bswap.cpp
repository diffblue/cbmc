/*******************************************************************\

Module: Bit-blasting of bswap

Author: Michael Tautschnig

\*******************************************************************/

#include "boolbv.h"

#include <util/config.h>
#include <util/invariant.h>

bvt boolbvt::convert_bswap(const bswap_exprt &expr)
{
  const std::size_t width = boolbv_width(expr.type());

  // width must be multiple of bytes
  const std::size_t byte_bits = config.ansi_c.char_width;
  if(width % byte_bits != 0)
    return conversion_failed(expr);

  bvt result = convert_bv(expr.op());
  CHECK_RETURN(result.size() == width);

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
