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
    int_value=binary2integer(id2string(value), false);
    return false;
  }
  else if(type_id==ID_signedbv)
  {
    int_value=binary2integer(id2string(value), true);
    return false;
  }
  else if(type_id==ID_c_bool)
  {
    int_value=binary2integer(id2string(value), false);
    return false;
  }
  else if(type_id==ID_c_enum)
  {
    const typet &subtype=to_c_enum_type(type).subtype();
    if(subtype.id()==ID_signedbv)
    {
      int_value=binary2integer(id2string(value), true);
      return false;
    }
    else if(subtype.id()==ID_unsignedbv)
    {
      int_value=binary2integer(id2string(value), false);
      return false;
    }
  }
  else if(type_id==ID_c_bit_field)
  {
    const typet &subtype=type.subtype();
    if(subtype.id()==ID_signedbv)
    {
      int_value=binary2integer(id2string(value), true);
      return false;
    }
    else if(subtype.id()==ID_unsignedbv)
    {
      int_value=binary2integer(id2string(value), false);
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
    uint_value=integer2unsigned(i);
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
    if(int_value<0)
    {
      constant_exprt r;
      r.make_nil();
      return r;
    }

    return constant_exprt(integer2string(int_value), type);
  }
  else if(type_id==ID_unsignedbv)
  {
    std::size_t width=to_unsignedbv_type(type).get_width();
    return constant_exprt(integer2binary(int_value, width), type);
  }
  else if(type_id==ID_bv)
  {
    std::size_t width=to_bv_type(type).get_width();
    return constant_exprt(integer2binary(int_value, width), type);
  }
  else if(type_id==ID_signedbv)
  {
    std::size_t width=to_signedbv_type(type).get_width();
    return constant_exprt(integer2binary(int_value, width), type);
  }
  else if(type_id==ID_c_enum)
  {
    const std::size_t width =
      to_c_enum_type(type).subtype().get_size_t(ID_width);
    return constant_exprt(integer2binary(int_value, width), type);
  }
  else if(type_id==ID_c_bool)
  {
    std::size_t width=to_c_bool_type(type).get_width();
    return constant_exprt(integer2binary(int_value, width), type);
  }
  else if(type_id==ID_bool)
  {
    if(int_value==0)
      return false_exprt();
    else if(int_value==1)
      return true_exprt();
  }
  else if(type_id==ID_pointer)
  {
    if(int_value==0)
      return null_pointer_exprt(to_pointer_type(type));
  }
  else if(type_id==ID_c_bit_field)
  {
    std::size_t width=to_c_bit_field_type(type).get_width();
    return constant_exprt(integer2binary(int_value, width), type);
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

  {
    PRECONDITION(false);
    constant_exprt r;
    r.make_nil();
    return r;
  }
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
