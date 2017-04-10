/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <cctype>
#include <cassert>
#include <vector>

#include <sstream>
#include <ostream>
#include <limits>

#include "mp_arith.h"
#include "arith_tools.h"

/*******************************************************************\

Function: >>

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

std::ostream &operator<<(std::ostream &out, const mp_integer &n)
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

const std::string integer2binary(const mp_integer &n, std::size_t width)
{
  mp_integer a(n);

  if(width==0)
    return "";

  bool neg=a.is_negative();

  if(neg)
  {
    a.negate();
    a=a-1;
  }

  std::size_t len = a.digits(2) + 2;
  std::vector<char> buffer(len);
  char *s = a.as_string(buffer.data(), len, 2);

  std::string result(s);

  if(result.size()<width)
  {
    std::string fill;
    fill.resize(width-result.size(), '0');
    result=fill+result;
  }
  else if(result.size()>width)
    result=result.substr(result.size()-width, width);

  if(neg)
  {
    for(std::size_t i=0; i<result.size(); i++)
      result[i]=(result[i]=='0')?'1':'0';
  }

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
  std::vector<char> buffer(len);
  char *s = n.as_string(buffer.data(), len, base);

  std::string result(s);

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
  if(n.empty())
    return 0;

  if(n.size()<=(sizeof(unsigned long)*8))
  {
    // this is a tuned implementation for short integers

    unsigned long mask=1;
    mask=mask << (n.size()-1);
    mp_integer top_bit=(n[0]=='1') ? mask : 0;
    if(is_signed)
      top_bit.negate();
    mask>>=1;
    unsigned long other_bits=0;

    for(std::string::const_iterator it=++n.begin();
        it!=n.end();
        ++it)
    {
      if(*it=='1')
        other_bits+=mask;
      else if(*it!='0')
        return 0;

      mask>>=1;
    }

    return top_bit+other_bits;
  }

  #if 0

  mp_integer mask=1;
  mask=mask << (n.size()-1);
  mp_integer result=(n[0]=='1') ? mask : 0;
  if(is_signed)
    result.negate();
  mask=mask>>1;

  for(std::string::const_iterator it=++n.begin();
      it!=n.end();
      ++it)
  {
    if(*it=='1')
      result+=mask;

    mask=mask>>1;
  }

  return result;

  #else
  if(n.find_first_not_of("01")!=std::string::npos)
    return 0;

  if(is_signed && n[0]=='1')
  {
    mp_integer result(n.c_str()+1, 2);
    result-=mp_integer(1)<<(n.size()-1);
    return result;
  }
  else
    return BigInt(n.c_str(), 2);

  #endif
}

/*******************************************************************\

Function: integer2ulong

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer::ullong_t integer2ulong(const mp_integer &n)
{
  assert(n.is_ulong());
  return n.to_ulong();
}

/*******************************************************************\

Function: integer2size_t

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::size_t integer2size_t(const mp_integer &n)
{
  assert(n>=0);
  mp_integer::ullong_t ull=integer2ulong(n);
  assert(ull <= std::numeric_limits<std::size_t>::max());
  return (std::size_t)ull;
}

/*******************************************************************\

Function: integer2unsigned

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned integer2unsigned(const mp_integer &n)
{
  assert(n>=0);
  mp_integer::ullong_t ull=integer2ulong(n);
  assert(ull <= std::numeric_limits<unsigned>::max());
  return (unsigned)ull;
}
