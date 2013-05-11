/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <cctype>

#include <sstream>

#include "mp_arith.h"
#include "arith_tools.h"

/*******************************************************************\

Function: >>

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#include <iostream>

mp_integer operator>>(const mp_integer &a, const mp_integer &b)
{
  mp_integer power=::power(2, b);
  
  if(a>=0)
    return a/power;
  else
  {
    // arithmetic shift right isn't division for negative numbers!
    // http://en.wikipedia.org/wiki/Arithmetic_shift 

    if((a%power)==0)
      return a/power;
    else
      return a/power-1;
  }
}

/*******************************************************************\

Function: <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer operator<<(const mp_integer &a, const mp_integer &b)
{
  return a*power(2, b);
}

/*******************************************************************\

Function: <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream& operator<<(std::ostream& out, const mp_integer &n)
{
  out << integer2string(n);
  return out;
}

/*******************************************************************\

Function: string2integer

  Inputs: string of '0'-'9' etc. most significant digit first
          base of number representation

 Outputs: mp_integer

 Purpose:

\*******************************************************************/

const mp_integer string2integer(const std::string &n, unsigned base)
{
  for(unsigned i=0; i<n.size(); i++)
    if(!(isalnum(n[i]) || (n[i]=='-' && i==0)))
      return 0;

  return mp_integer(n.c_str(), base);
}

/*******************************************************************\

Function: integer2binary

  Inputs:

 Outputs: string of '0'/'1', most significant bit first

 Purpose:

\*******************************************************************/

const std::string integer2binary(const mp_integer &n, unsigned width)
{
  mp_integer a(n);

  if(width==0) return "";

  bool neg=a.is_negative();

  if(neg)
  {
    a.negate();
    a=a-1;
  }

  unsigned len = a.digits(2) + 2;
  char *buffer=(char *)malloc(len);
  char *s = a.as_string(buffer, len, 2);

  std::string result(s);

  free(buffer);

  if(result.size()<width)
  {
    std::string fill;
    fill.resize(width-result.size(), '0');
    result=fill+result;
  }
  else if(result.size()>width)
    result=result.substr(result.size()-width, width);

  if(neg)
    for(unsigned i=0; i<result.size(); i++)
      result[i]=(result[i]=='0')?'1':'0';

  return result;
}

/*******************************************************************\

Function: integer2string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string integer2string(const mp_integer &n, unsigned base)
{
  unsigned len = n.digits(base) + 2;
  char *buffer=(char *)malloc(len);
  char *s = n.as_string(buffer, len, base);

  std::string result(s);

  free(buffer);

  return result;
}

/*******************************************************************\

Function: binary2integer

  Inputs: string of '0'/'1', most significant bit first

 Outputs: mp_integer

 Purpose: convert binary string representation to mp_integer

\*******************************************************************/

const mp_integer binary2integer(const std::string &n, bool is_signed)
{
  if(n.size()==0) return 0;

  mp_integer result=0;
  mp_integer mask=1;
  mask=mask << (n.size()-1);

  for(unsigned i=0; i<n.size(); i++)
  {
    if(n[i]=='0')
    {
    }
    else if(n[i]=='1')
    {
      if(is_signed && i==0)
        result=-mask;
      else
        result=result+mask;
    }
    else
      return 0;

    mask=mask>>1;
  }

  return result;
}

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned long integer2long(const mp_integer &n)
{
  return n.to_ulong();
}
