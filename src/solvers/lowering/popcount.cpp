/*******************************************************************\

Module: Lowering of popcount

Author: Michael Tautschnig

\*******************************************************************/

#include "expr_lowering.h"

#include <util/arith_tools.h>
#include <util/invariant.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>

exprt lower_popcount(const popcount_exprt &expr, const namespacet &ns)
{
  // Hacker's Delight, variant pop0:
  // x = (x & 0x55555555) + ((x >> 1) & 0x55555555);
  // x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
  // x = (x & 0x0F0F0F0F) + ((x >> 4) & 0x0F0F0F0F);
  // x = (x & 0x00FF00FF) + ((x >> 8) & 0x00FF00FF);
  // etc.
  // return x;
  // http://www.hackersdelight.org/permissions.htm

  // make sure the operand width is a power of two
  exprt x = expr.op();
  const auto x_width = pointer_offset_bits(x.type(), ns);
  CHECK_RETURN(x_width.has_value() && *x_width >= 1);
  const std::size_t bits = address_bits(*x_width);
  const std::size_t new_width = integer2size_t(power(2, bits));
  const bool need_typecast =
    new_width > *x_width || x.type().id() != ID_unsignedbv;
  if(need_typecast)
    x.make_typecast(unsignedbv_typet(new_width));

  // repeatedly compute x = (x & bitmask) + ((x >> shift) & bitmask)
  for(std::size_t shift = 1; shift < new_width; shift <<= 1)
  {
    // x >> shift
    lshr_exprt shifted_x(
      x, from_integer(shift, unsignedbv_typet(address_bits(shift) + 1)));
    // bitmask is a string of alternating shift-many bits starting from lsb set
    // to 1
    std::string bitstring;
    bitstring.reserve(new_width);
    for(std::size_t i = 0; i < new_width / (2 * shift); ++i)
      bitstring += std::string(shift, '0') + std::string(shift, '1');
    const mp_integer value = binary2integer(bitstring, false);
    const constant_exprt bitmask(integer2bvrep(value, new_width), x.type());
    // build the expression
    x = plus_exprt(bitand_exprt(x, bitmask), bitand_exprt(shifted_x, bitmask));
  }

  // the result is restricted to the result type
  x.make_typecast(expr.type());

  return x;
}
