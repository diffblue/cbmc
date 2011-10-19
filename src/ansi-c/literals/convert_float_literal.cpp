/*******************************************************************\

Module: C++ Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>
#include <stdlib.h>

#include <arith_tools.h>
#include <config.h>
#include <ieee_float.h>
#include <std_types.h>

#include "../c_types.h"
#include "parse_float.h"
#include "convert_float_literal.h"

/*******************************************************************\

Function: convert_float_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt convert_float_literal(const std::string &src)
{
  mp_integer significand;
  mp_integer exponent;
  bool is_float, is_long;
  
  parse_float(src, significand, exponent, is_float, is_long);

  exprt result=exprt(ID_constant);
  
  result.set(ID_C_cformat, src);
  
  // In ANSI-C, float literals are double by default
  // unless marked with 'f'.

  if(is_float)
    result.type()=float_type();
  else if(is_long)
    result.type()=long_double_type();
  else
    result.type()=double_type(); // default

  if(config.ansi_c.use_fixed_for_float)
  {
    unsigned width=result.type().get_int(ID_width);
    unsigned fraction_bits;
    const irep_idt integer_bits=result.type().get(ID_integer_bits);
    
    assert(width!=0);

    if(integer_bits==irep_idt())
      fraction_bits=width/2; // default
    else
      fraction_bits=width-atoi(integer_bits.c_str());

    mp_integer factor=mp_integer(1)<<fraction_bits;
    mp_integer value=significand*factor;
    
    if(value!=0)
    {
      if(exponent<0)
        value/=power(10, -exponent);
      else
      {
        value*=power(10, exponent);    

        if(value>=power(2, width-1))
        {
          // saturate: use "biggest value"
          value=power(2, width-1)-1;
        }
        else if(value<=-power(2, width-1)-1)
        {
          // saturate: use "smallest value"
          value=-power(2, width-1);
        }
      }
    }

    result.set(ID_value, integer2binary(value, width));  
  }
  else
  {
    ieee_floatt a;

    a.spec=to_floatbv_type(result.type());
    a.from_base10(significand, exponent);

    result.set(ID_value,
      integer2binary(a.pack(), a.spec.width()));  
  }
  
  return result;
}
