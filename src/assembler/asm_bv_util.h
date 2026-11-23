/*******************************************************************\

Module: Inline assembly: bit-vector helpers for instruction semantics

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Bit-vector helpers shared by the instruction semantics of all
/// architectures. All values are of type unsignedbv; signedness is a property
/// of operations, as in the hardware.

#ifndef CPROVER_ASSEMBLER_ASM_BV_UTIL_H
#define CPROVER_ASSEMBLER_ASM_BV_UTIL_H

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/std_expr.h>

namespace asm_bv // NOLINT
{
inline unsignedbv_typet bv(std::size_t width)
{
  return unsignedbv_typet{width};
}

inline exprt constant(const mp_integer &value, std::size_t width)
{
  // reduce modulo 2^width so that negative values wrap
  const mp_integer modulus = power(2, width);
  mp_integer v = value % modulus;
  if(v < 0)
    v += modulus;
  return from_integer(v, bv(width));
}

/// \p value converted to \p width bits, truncating or zero-extending
inline exprt resize(const exprt &value, std::size_t width)
{
  return typecast_exprt::conditional_cast(value, bv(width));
}

/// \p value sign-extended from \p from to \p to bits
inline exprt sign_extend(const exprt &value, std::size_t from, std::size_t to)
{
  return typecast_exprt{
    typecast_exprt{resize(value, from), signedbv_typet{from}}, bv(to)};
}

inline exprt msb(const exprt &value, std::size_t width)
{
  return extractbit_exprt{value, width - 1};
}

inline exprt is_zero(const exprt &value)
{
  return equal_exprt{value, from_integer(0, value.type())};
}

/// the bits of \p storage with bits [offset, offset+width) replaced by
/// \p value
inline exprt replace_bits(
  const exprt &storage,
  std::size_t storage_width,
  std::size_t offset,
  std::size_t width,
  const exprt &value)
{
  if(offset == 0 && width == storage_width)
    return resize(value, storage_width);

  const mp_integer mask = (power(2, width) - 1) * power(2, offset);
  const mp_integer all = power(2, storage_width) - 1;
  exprt shifted = resize(value, storage_width);
  if(offset != 0)
    shifted = shl_exprt{shifted, offset};
  return bitor_exprt{
    bitand_exprt{storage, from_integer(all - mask, bv(storage_width))},
    shifted};
}

/// bits [offset, offset+width) of \p storage
inline exprt
extract(const exprt &storage, std::size_t offset, std::size_t width)
{
  return extractbits_exprt{storage, offset, bv(width)};
}

/// carry out of \p a + \p b + \p carry_in (Boolean)
inline exprt carry_add(
  const exprt &a,
  const exprt &b,
  const exprt &carry_in,
  std::size_t width)
{
  const exprt sum = plus_exprt{
    plus_exprt{resize(a, width + 1), resize(b, width + 1)},
    resize(carry_in, width + 1)};
  return extractbit_exprt{sum, width};
}

/// borrow out of \p a - \p b - \p borrow_in (Boolean), i.e., the unsigned
/// value of a is less than that of b + borrow_in
inline exprt borrow_sub(
  const exprt &a,
  const exprt &b,
  const exprt &borrow_in,
  std::size_t width)
{
  const exprt diff = minus_exprt{
    minus_exprt{resize(a, width + 1), resize(b, width + 1)},
    resize(borrow_in, width + 1)};
  return extractbit_exprt{diff, width};
}

/// signed overflow of \p result = \p a + \p b
inline exprt
overflow_add(const exprt &a, const exprt &b, const exprt &result, std::size_t w)
{
  return and_exprt{
    equal_exprt{msb(a, w), msb(b, w)},
    notequal_exprt{msb(result, w), msb(a, w)}};
}

/// signed overflow of \p result = \p a - \p b
inline exprt
overflow_sub(const exprt &a, const exprt &b, const exprt &result, std::size_t w)
{
  return and_exprt{
    notequal_exprt{msb(a, w), msb(b, w)},
    notequal_exprt{msb(result, w), msb(a, w)}};
}

/// a Boolean as a one-bit value
inline exprt bool_to_bv(const exprt &b, std::size_t width)
{
  return if_exprt{b, from_integer(1, bv(width)), from_integer(0, bv(width))};
}

/// true if the low byte of \p value has an even number of set bits
inline exprt even_parity_low_byte(const exprt &value)
{
  exprt::operandst bits;
  for(std::size_t i = 0; i < 8; ++i)
    bits.push_back(extractbit_exprt{value, i});
  exprt x = bits[0];
  for(std::size_t i = 1; i < 8; ++i)
    x = xor_exprt{x, bits[i]};
  return not_exprt{x};
}
} // namespace asm_bv

#endif // CPROVER_ASSEMBLER_ASM_BV_UTIL_H
