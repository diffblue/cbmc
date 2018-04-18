/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "arith_tools.h"

#include "fixedbv.h"
#include "ieee_float.h"
#include "invariant.h"
#include "std_types.h"
#include "std_expr.h"

#include <algorithm>

bool to_integer(const exprt &expr, mp_integer &int_value)
{
  if(!expr.is_constant())
    return true;
  return to_integer(to_constant_expr(expr), int_value);
}

bool to_integer(const constant_exprt &expr, mp_integer &int_value)
{
  const irep_idt &value=expr.get_value();
  const typet &type=expr.type();
  const irep_idt &type_id=type.id();

  if(type_id==ID_pointer)
  {
    if(value==ID_NULL)
    {
      int_value=0;
      return false;
    }
  }
  else if(type_id==ID_integer ||
          type_id==ID_natural)
  {
    int_value=string2integer(id2string(value));
    return false;
  }
  else if(type_id==ID_unsignedbv)
  {
    const auto width = to_unsignedbv_type(type).get_width();
    int_value = bvrep2integer(value, width, false);
    return false;
  }
  else if(type_id==ID_signedbv)
  {
    const auto width = to_signedbv_type(type).get_width();
    int_value = bvrep2integer(value, width, true);
    return false;
  }
  else if(type_id==ID_c_bool)
  {
    const auto width = to_c_bool_type(type).get_width();
    int_value = bvrep2integer(value, width, false);
    return false;
  }
  else if(type_id==ID_c_enum)
  {
    const typet &subtype=to_c_enum_type(type).subtype();
    if(subtype.id()==ID_signedbv)
    {
      const auto width = to_signedbv_type(type).get_width();
      int_value = bvrep2integer(value, width, true);
      return false;
    }
    else if(subtype.id()==ID_unsignedbv)
    {
      const auto width = to_unsignedbv_type(type).get_width();
      int_value = bvrep2integer(value, width, false);
      return false;
    }
  }
  else if(type_id==ID_c_bit_field)
  {
    const auto &c_bit_field_type = to_c_bit_field_type(type);
    const auto width = c_bit_field_type.get_width();
    const typet &subtype = c_bit_field_type.subtype();

    if(subtype.id()==ID_signedbv)
    {
      int_value = bvrep2integer(value, width, true);
      return false;
    }
    else if(subtype.id()==ID_unsignedbv)
    {
      int_value = bvrep2integer(value, width, false);
      return false;
    }
    else if(subtype.id() == ID_c_bool)
    {
      int_value = bvrep2integer(value, width, false);
      return false;
    }
  }

  return true;
}

/// convert a positive integer expression to an unsigned int
/// \par parameters: a constant expression and a reference to an unsigned int
/// \return an error flag
bool to_unsigned_integer(const constant_exprt &expr, unsigned &uint_value)
{
  mp_integer i;
  if(to_integer(expr, i))
    return true;
  if(i<0)
    return true;
  else
  {
    uint_value = numeric_cast_v<unsigned>(i);
    return false;
  }
}

constant_exprt from_integer(
  const mp_integer &int_value,
  const typet &type)
{
  const irep_idt &type_id=type.id();

  if(type_id==ID_integer)
  {
    return constant_exprt(integer2string(int_value), type);
  }
  else if(type_id==ID_natural)
  {
    PRECONDITION(int_value >= 0);
    return constant_exprt(integer2string(int_value), type);
  }
  else if(type_id==ID_unsignedbv)
  {
    std::size_t width=to_unsignedbv_type(type).get_width();
    return constant_exprt(integer2bvrep(int_value, width), type);
  }
  else if(type_id==ID_bv)
  {
    std::size_t width=to_bv_type(type).get_width();
    return constant_exprt(integer2bvrep(int_value, width), type);
  }
  else if(type_id==ID_signedbv)
  {
    std::size_t width=to_signedbv_type(type).get_width();
    return constant_exprt(integer2bvrep(int_value, width), type);
  }
  else if(type_id==ID_c_enum)
  {
    const std::size_t width =
      to_bitvector_type(to_c_enum_type(type).subtype()).get_width();
    return constant_exprt(integer2bvrep(int_value, width), type);
  }
  else if(type_id==ID_c_bool)
  {
    std::size_t width=to_c_bool_type(type).get_width();
    return constant_exprt(integer2bvrep(int_value, width), type);
  }
  else if(type_id==ID_bool)
  {
    PRECONDITION(int_value == 0 || int_value == 1);
    if(int_value == 0)
      return false_exprt();
    else
      return true_exprt();
  }
  else if(type_id==ID_pointer)
  {
    PRECONDITION(int_value == 0);
    return null_pointer_exprt(to_pointer_type(type));
  }
  else if(type_id==ID_c_bit_field)
  {
    std::size_t width=to_c_bit_field_type(type).get_width();
    return constant_exprt(integer2bvrep(int_value, width), type);
  }
  else if(type_id==ID_fixedbv)
  {
    fixedbvt fixedbv;
    fixedbv.spec=fixedbv_spect(to_fixedbv_type(type));
    fixedbv.from_integer(int_value);
    return fixedbv.to_expr();
  }
  else if(type_id==ID_floatbv)
  {
    ieee_floatt ieee_float(to_floatbv_type(type));
    ieee_float.from_integer(int_value);
    return ieee_float.to_expr();
  }
  else
    PRECONDITION(false);
}

/// ceil(log2(size))
std::size_t address_bits(const mp_integer &size)
{
  // in theory an arbitrary-precision integer could be as large as
  // numeric_limits<std::size_t>::max() * CHAR_BIT (but then we would only be
  // able to store 2^CHAR_BIT many of those; the implementation of mp_integer as
  // BigInt is much more restricted as its size is stored as an unsigned int
  std::size_t result = 1;

  for(mp_integer x = 2; x < size; ++result, x *= 2) {}

  INVARIANT(power(2, result) >= size, "address_bits(size) >= log2(size)");

  return result;
}

/// A multi-precision implementation of the power operator.
/// \par parameters: Two mp_integers, base and exponent
/// \return One mp_integer with the value base^{exponent}
mp_integer power(const mp_integer &base,
                 const mp_integer &exponent)
{
  PRECONDITION(exponent >= 0);

  /* There are a number of special cases which are:
   *  A. very common
   *  B. handled more efficiently
   */
  if(base.is_long() && exponent.is_long())
  {
    switch(base.to_long())
    {
    case 2:
      {
        mp_integer result;
        result.setPower2(exponent.to_ulong());
        return result;
      }
    case 1: return 1;
    case 0: return 0;
    default:
      {
      }
    }
  }

  if(exponent==0)
    return 1;

  if(base<0)
  {
    mp_integer result = power(-base, exponent);
    if(exponent.is_odd())
      return -result;
    else
      return result;
  }

  mp_integer result=base;
  mp_integer count=exponent-1;

  while(count!=0)
  {
    result*=base;
    --count;
  }

  return result;
}

void mp_min(mp_integer &a, const mp_integer &b)
{
  if(b<a)
    a=b;
}

void mp_max(mp_integer &a, const mp_integer &b)
{
  if(b>a)
    a=b;
}

/// Get a bit with given index from bit-vector representation.
/// \param src: the bitvector representation
/// \param width: the number of bits in the bitvector
/// \param bit_index: index (0 is the least significant)
bool get_bvrep_bit(
  const irep_idt &src,
  std::size_t width,
  std::size_t bit_index)
{
  PRECONDITION(bit_index < width);

  // The representation is hex, i.e., four bits per letter,
  // most significant nibble first, using uppercase letters.
  // No lowercase, no leading zeros (other than for 'zero'),
  // to ensure canonicity.
  const auto nibble_index = bit_index / 4;

  if(nibble_index >= src.size())
    return false;

  const char nibble = src[src.size() - 1 - nibble_index];

  DATA_INVARIANT(
    isdigit(nibble) || (nibble >= 'A' && nibble <= 'F'),
    "bvrep is hexadecimal, upper-case");

  const unsigned char nibble_value =
    isdigit(nibble) ? nibble - '0' : nibble - 'A' + 10;

  return ((nibble_value >> (bit_index % 4)) & 1) != 0;
}

/// turn a value 0...15 into '0'-'9', 'A'-'Z'
static char nibble2hex(unsigned char nibble)
{
  PRECONDITION(nibble <= 0xf);

  if(nibble >= 10)
    return 'A' + nibble - 10;
  else
    return '0' + nibble;
}

/// construct a bit-vector representation from a functor
/// \param width: the width of the bit-vector
/// \param f: the functor -- the parameter is the bit index
/// \return new bitvector representation
irep_idt
make_bvrep(const std::size_t width, const std::function<bool(std::size_t)> f)
{
  std::string result;
  result.reserve((width + 3) / 4);
  unsigned char nibble = 0;

  for(std::size_t i = 0; i < width; i++)
  {
    const auto bit_in_nibble = i % 4;

    nibble |= ((unsigned char)f(i)) << bit_in_nibble;

    if(bit_in_nibble == 3)
    {
      result += nibble2hex(nibble);
      nibble = 0;
    }
  }

  if(nibble != 0)
    result += nibble2hex(nibble);

  // drop leading zeros
  const std::size_t pos = result.find_last_not_of('0');

  if(pos == std::string::npos)
    return ID_0;
  else
  {
    result.resize(pos + 1);

    std::reverse(result.begin(), result.end());

    return result;
  }
}

/// perform a binary bit-wise operation, given as a functor,
/// on a bit-vector representation
/// \param a: the representation of the first bit vector
/// \param b: the representation of the second bit vector
/// \param width: the width of the bit-vector
/// \param f: the functor
/// \return new bitvector representation
irep_idt bvrep_bitwise_op(
  const irep_idt &a,
  const irep_idt &b,
  const std::size_t width,
  const std::function<bool(bool, bool)> f)
{
  return make_bvrep(width, [&a, &b, &width, f](std::size_t i) {
    return f(get_bvrep_bit(a, width, i), get_bvrep_bit(b, width, i));
  });
}

/// perform a unary bit-wise operation, given as a functor,
/// on a bit-vector representation
/// \param a: the bit-vector representation
/// \param width: the width of the bit-vector
/// \param f: the functor
/// \return new bitvector representation
irep_idt bvrep_bitwise_op(
  const irep_idt &a,
  const std::size_t width,
  const std::function<bool(bool)> f)
{
  return make_bvrep(width, [&a, &width, f](std::size_t i) {
    return f(get_bvrep_bit(a, width, i));
  });
}

/// convert an integer to bit-vector representation with given width
/// This uses two's complement for negative numbers.
/// If the value is out of range, it is 'wrapped around'.
irep_idt integer2bvrep(const mp_integer &src, std::size_t width)
{
  const mp_integer p = power(2, width);

  if(src.is_negative())
  {
    // do two's complement encoding of negative numbers
    mp_integer tmp = src;
    tmp.negate();
    tmp %= p;
    if(tmp != 0)
      tmp = p - tmp;
    return integer2string(tmp, 16);
  }
  else
  {
    // we 'wrap around' if 'src' is too large
    return integer2string(src % p, 16);
  }
}

/// convert a bit-vector representation (possibly signed) to integer
mp_integer bvrep2integer(const irep_idt &src, std::size_t width, bool is_signed)
{
  if(is_signed)
  {
    PRECONDITION(width >= 1);
    const auto tmp = string2integer(id2string(src), 16);
    const auto p = power(2, width - 1);
    if(tmp >= p)
    {
      const auto result = tmp - 2 * p;
      PRECONDITION(result >= -p);
      return result;
    }
    else
      return tmp;
  }
  else
  {
    const auto result = string2integer(id2string(src), 16);
    PRECONDITION(result < power(2, width));
    return result;
  }
}
