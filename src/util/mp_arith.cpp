/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "mp_arith.h"

#include <cstdlib>
#include <cctype>
#include <cassert>

#include <sstream>
#include <ostream>
#include <limits>

#include "arith_tools.h"


typedef BigInt::ullong_t ullong_t; // NOLINT(readability/identifiers)
typedef BigInt::llong_t llong_t; // NOLINT(readability/identifiers)

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

mp_integer operator<<(const mp_integer &a, const mp_integer &b)
{
  return a*power(2, b);
}

std::ostream &operator<<(std::ostream &out, const mp_integer &n)
{
  out << integer2string(n);
  return out;
}

/// \par parameters: string of '0'-'9' etc. most significant digit first
/// base of number representation
/// \return mp_integer
const mp_integer string2integer(const std::string &n, unsigned base)
{
  for(unsigned i=0; i<n.size(); i++)
    if(!(isalnum(n[i]) || (n[i]=='-' && i==0)))
      return 0;

  return mp_integer(n.c_str(), base);
}

/// \return string of '0'/'1', most significant bit first
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
  char *buffer=new char[len];
  char *s = a.as_string(buffer, len, 2);

  std::string result(s);

  delete[] buffer;

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

const std::string integer2string(const mp_integer &n, unsigned base)
{
  unsigned len = n.digits(base) + 2;
  char *buffer=new char[len];
  char *s = n.as_string(buffer, len, base);

  std::string result(s);

  delete[] buffer;

  return result;
}

/// convert binary string representation to mp_integer
/// \par parameters: string of '0'/'1', most significant bit first
/// \return mp_integer
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

mp_integer::ullong_t integer2ulong(const mp_integer &n)
{
  assert(n.is_ulong());
  return n.to_ulong();
}

std::size_t integer2size_t(const mp_integer &n)
{
  assert(n>=0);
  mp_integer::ullong_t ull=integer2ulong(n);
  assert(ull <= std::numeric_limits<std::size_t>::max());
  return (std::size_t)ull;
}

unsigned integer2unsigned(const mp_integer &n)
{
  assert(n>=0);
  mp_integer::ullong_t ull=integer2ulong(n);
  assert(ull <= std::numeric_limits<unsigned>::max());
  return (unsigned)ull;
}

/// bitwise or bitwise operations only make sense on native objects, hence the
/// largest object size should be the largest available c++ integer size
/// (currently long long)
mp_integer bitwise_or(const mp_integer &a, const mp_integer &b)
{
  ullong_t result=a.to_ulong()|b.to_ulong();
  return result;
}

/// bitwise and bitwise operations only make sense on native objects, hence the
/// largest object size should be the largest available c++ integer size
/// (currently long long)
mp_integer bitwise_and(const mp_integer &a, const mp_integer &b)
{
  ullong_t result=a.to_ulong()&b.to_ulong();
  return result;
}

/// bitwise xor bitwise operations only make sense on native objects, hence the
/// largest object size should be the largest available c++ integer size
/// (currently long long)
mp_integer bitwise_xor(const mp_integer &a, const mp_integer &b)
{
  ullong_t result=a.to_ulong()^b.to_ulong();
  return result;
}

/// bitwise negation bitwise operations only make sense on native objects, hence
/// the largest object size should be the largest available c++ integer size
/// (currently long long)
mp_integer bitwise_neg(const mp_integer &a)
{
  ullong_t result=~a.to_ulong();
  return result;
}

/// arithmetic left shift bitwise operations only make sense on native objects,
/// hence the largest object size should be the largest available c++ integer
/// size (currently long long)
mp_integer arith_left_shift(
  const mp_integer &a,
  const mp_integer &b,
  std::size_t true_size)
{
  ullong_t shift=b.to_ulong();
  if(shift>true_size && a!=mp_integer(0))
    throw "shift value out of range";

  llong_t result=a.to_long()<<shift;
  llong_t mask=
    true_size<(sizeof(llong_t)*8) ?
    (1L<<true_size)-1 :
    -1;
  return result&mask;
}

/// arithmetic right shift (loads sign on MSB) bitwise operations only make
/// sense on native objects, hence the largest object size should be the largest
/// available c++ integer size (currently long long)
mp_integer arith_right_shift(
  const mp_integer &a,
  const mp_integer &b,
  std::size_t true_size)
{
  llong_t number=a.to_long();
  ullong_t shift=b.to_ulong();
  if(shift>true_size)
    throw "shift value out of range";

  llong_t sign=(1<<(true_size-1))&number;
  llong_t pad=(sign==0) ? 0 : ~((1<<(true_size-shift))-1);
  llong_t result=(number >> shift)|pad;
  return result;
}

/// logic left shift bitwise operations only make sense on native objects, hence
/// the largest object size should be the largest available c++ integer size
/// (currently long long)
mp_integer logic_left_shift(
  const mp_integer &a,
  const mp_integer &b,
  std::size_t true_size)
{
  ullong_t shift=b.to_ulong();
  if(shift>true_size && a!=mp_integer(0))
    throw "shift value out of range";
  llong_t result=a.to_long()<<shift;
  if(true_size<(sizeof(llong_t)*8))
  {
    llong_t sign=(1L<<(true_size-1))&result;
    llong_t mask=(1L<<true_size)-1;
    // Sign-fill out-of-range bits:
    if(sign==0)
      result&=mask;
    else
      result|=~mask;
  }
  return result;
}

/// logic right shift (loads 0 on MSB) bitwise operations only make sense on
/// native objects, hence the largest object size should be the largest
/// available c++ integer size (currently long long)
mp_integer logic_right_shift(
  const mp_integer &a,
  const mp_integer &b,
  std::size_t true_size)
{
  ullong_t shift=b.to_ulong();
  if(shift>true_size)
    throw "shift value out of range";

  ullong_t result=((ullong_t)a.to_long()) >> shift;
  return result;
}

/// rotates right (MSB=LSB) bitwise operations only make sense on native
/// objects, hence the largest object size should be the largest available c++
/// integer size (currently long long)
mp_integer rotate_right(
  const mp_integer &a,
  const mp_integer &b,
  std::size_t true_size)
{
  ullong_t number=a.to_ulong();
  ullong_t shift=b.to_ulong();
  if(shift>true_size)
    throw "shift value out of range";

  ullong_t revShift=true_size-shift;
  ullong_t filter=1<<(true_size-1);
  ullong_t result=(number >> shift)|((number<<revShift)&filter);
  return result;
}

/// rotate left (LSB=MSB) bitwise operations only make sense on native objects,
/// hence the largest object size should be the largest available c++ integer
/// size (currently long long)
mp_integer rotate_left(
  const mp_integer &a,
  const mp_integer &b,
  std::size_t true_size)
{
  ullong_t number=a.to_ulong();
  ullong_t shift=b.to_ulong();
  if(shift>true_size)
    throw "shift value out of range";

  ullong_t revShift=true_size-shift;
  ullong_t filter=1<<(true_size-1);
  ullong_t result=((number<<shift)&filter)|((number&filter) >> revShift);
  return result;
}
