/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "arith_tools.h"
#include "std_types.h"
#include "std_expr.h"

/*******************************************************************\

Function: to_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool to_integer(const exprt &expr, mp_integer &int_value)
{
  if(!expr.is_constant()) return true;
  return to_integer(to_constant_expr(expr), int_value);
}

/*******************************************************************\

Function: to_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: from_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt from_integer(
  const mp_integer &int_value,
  const typet &type)
{
  const irep_idt &type_id=type.id();

  if(type_id==ID_integer)
  {
    constant_exprt result(type);
    result.set_value(integer2string(int_value));
    return result;
  }
  else if(type_id==ID_natural)
  {
    if(int_value<0) { constant_exprt r; r.make_nil(); return r; }
    constant_exprt result(type);
    result.set_value(integer2string(int_value));
    return result;
  }
  else if(type_id==ID_unsignedbv)
  {
    unsigned width=to_unsignedbv_type(type).get_width();
    constant_exprt result(type);
    result.set_value(integer2binary(int_value, width));
    return result;
  }
  else if(type_id==ID_bv)
  {
    unsigned width=to_bv_type(type).get_width();
    constant_exprt result(type);
    result.set_value(integer2binary(int_value, width));
    return result;
  }
  else if(type_id==ID_signedbv)
  {
    unsigned width=to_signedbv_type(type).get_width();
    constant_exprt result(type);
    result.set_value(integer2binary(int_value, width));
    return result;
  }
  else if(type_id==ID_c_enum)
  {
    unsigned width=to_c_enum_type(type).subtype().get_unsigned_int(ID_width);
    constant_exprt result(type);
    result.set_value(integer2binary(int_value, width));
    return result;
  }
  else if(type_id==ID_c_bool)
  {
    unsigned width=to_c_bool_type(type).get_width();
    constant_exprt result(type);
    result.set_value(integer2binary(int_value, width));
    return result;
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
    {
      constant_exprt result(type);
      result.set_value(ID_NULL);
      return result;
    }
  }
  else if(type_id==ID_c_bit_field)
  {
    unsigned width=to_c_bit_field_type(type).get_width();
    constant_exprt result(type);
    result.set_value(integer2binary(int_value, width));
    return result;
  }

  {
    constant_exprt r;
    r.make_nil();
    return r;
  }
}

/*******************************************************************\

Function: address_bits

  Inputs:

 Outputs:

 Purpose: ceil(log2(size))

\*******************************************************************/

mp_integer address_bits(const mp_integer &size)
{
  mp_integer result, x=2;

  for(result=1; x<size; result+=1, x*=2);

  return result;
}

/*******************************************************************\

Function: power

  Inputs: Two mp_integers, base and exponent

 Outputs: One mp_integer with the value base^{exponent}

 Purpose: A multi-precision implementation of the power operator.

\*******************************************************************/

mp_integer power(const mp_integer &base,
                 const mp_integer &exponent)
{
  assert(exponent>=0);

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
    default:;
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

/*******************************************************************\

Function: mp_min

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void mp_min(mp_integer &a, const mp_integer &b)
{
  if(b<a) a=b;
}

/*******************************************************************\

Function: mp_max

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void mp_max(mp_integer &a, const mp_integer &b)
{
  if(b>a) a=b;
}
