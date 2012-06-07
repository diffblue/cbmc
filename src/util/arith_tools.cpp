/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include "arith_tools.h"
#include "std_types.h"

/*******************************************************************\

Function: to_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool to_integer(const exprt &expr, mp_integer &int_value)
{
  if(!expr.is_constant()) return true;

  const std::string &value=expr.get_string(ID_value);
  const irep_idt &type_id=expr.type().id();

  if(type_id==ID_pointer)
  {
    if(value=="NULL")
    {
      int_value=0;
      return false;
    }
  }
  else if(type_id==ID_integer ||
          type_id==ID_natural ||
          type_id==ID_c_enum)
  {
    int_value=string2integer(value);
    return false;
  }
  else if(type_id==ID_unsignedbv)
  {
    int_value=binary2integer(value, false);
    return false;
  }
  else if(type_id==ID_signedbv)
  {
    int_value=binary2integer(value, true);
    return false;
  }

  return true;
}

/*******************************************************************\

Function: from_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt from_integer(
  const mp_integer &int_value,
  const typet &type)
{
  exprt expr;

  expr.clear();
  expr.type()=type;
  expr.id(ID_constant);

  const irep_idt &type_id=type.id();

  if(type_id==ID_integer)
  {
    expr.set(ID_value, integer2string(int_value));
    return expr;
  }
  else if(type_id==ID_natural)
  {
    if(int_value<0) { expr.make_nil(); return expr; }
    expr.set(ID_value, integer2string(int_value));
    return expr;
  }
  else if(type_id==ID_unsignedbv)
  {
    unsigned width=to_unsignedbv_type(type).get_width();
    expr.set(ID_value, integer2binary(int_value, width));
    return expr;
  }
  else if(type_id==ID_signedbv)
  {
    unsigned width=to_signedbv_type(type).get_width();
    expr.set(ID_value, integer2binary(int_value, width));
    return expr;
  }
  else if(type_id==ID_bool)
  {
    if(int_value==0)
    {
      expr.make_false();
      return expr;
    }
    else if(int_value==1)
    {
      expr.make_true();
      return expr;
    }
  }
  else if(type_id==ID_c_bool)
  {
    unsigned width=to_c_bool_type(type).get_width();

    if(int_value==0)
      expr.set(ID_value, integer2binary(0, width));
    else
      expr.set(ID_value, integer2binary(1, width));

    return expr;
  }

  expr.make_nil();
  return expr;
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

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer power(const mp_integer &base,
                 const mp_integer &exponent)
{
  assert(exponent>=0);

  if(exponent==0)
    return 1;

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
