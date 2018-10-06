/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "mp_arith.h"

#include <cctype>
#include <cstdlib>
#include <limits>
#include <ostream>
#include <sstream>
#include <vector>

#include "arith_tools.h"
#include "invariant.h"

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
  for(std::size_t i=0; i<n.size(); i++)
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

const std::string integer2string(const mp_integer &n, unsigned base)
{
  unsigned len = n.digits(base) + 2;
  std::vector<char> buffer(len);
  char *s = n.as_string(buffer.data(), len, base);

  std::string result(s);

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

/// convert an integer to bit-vector representation with given width
const std::string integer2bv(const mp_integer &src, std::size_t width)
{
  return integer2binary(src, width);
}

/// convert a bit-vector representation (possibly signed) to integer
const mp_integer bv2integer(const std::string &src, bool is_signed)
{
  return binary2integer(src, is_signed);
}

mp_integer::ullong_t integer2ulong(const mp_integer &n)
{
  PRECONDITION(n.is_ulong());
  return n.to_ulong();
}

std::size_t integer2size_t(const mp_integer &n)
{
  PRECONDITION(n>=0 && n<=std::numeric_limits<std::size_t>::max());
  PRECONDITION(n.is_ulong());
  mp_integer::ullong_t ull = n.to_ulong();
  return (std::size_t) ull;
}

unsigned integer2unsigned(const mp_integer &n)
{
  PRECONDITION(n>=0 && n<=std::numeric_limits<unsigned>::max());
  PRECONDITION(n.is_ulong());
  mp_integer::ullong_t ull = n.to_ulong();
  return (unsigned)ull;
}

/// bitwise or bitwise operations only make sense on native objects, hence the
/// largest object size should be the largest available c++ integer size
/// (currently long long)
mp_integer bitwise_or(const mp_integer &a, const mp_integer &b)
{
  PRECONDITION(a.is_ulong() && b.is_ulong());
  ullong_t result=a.to_ulong()|b.to_ulong();
  return result;
}

/// bitwise and bitwise operations only make sense on native objects, hence the
/// largest object size should be the largest available c++ integer size
/// (currently long long)
mp_integer bitwise_and(const mp_integer &a, const mp_integer &b)
{
  PRECONDITION(a.is_ulong() && b.is_ulong());
  ullong_t result=a.to_ulong()&b.to_ulong();
  return result;
}

/// bitwise xor bitwise operations only make sense on native objects, hence the
/// largest object size should be the largest available c++ integer size
/// (currently long long)
mp_integer bitwise_xor(const mp_integer &a, const mp_integer &b)
{
  PRECONDITION(a.is_ulong() && b.is_ulong());
  ullong_t result=a.to_ulong()^b.to_ulong();
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
  PRECONDITION(a.is_long() && b.is_ulong());
  PRECONDITION(b <= true_size || a == 0);

  ullong_t shift=b.to_ulong();

  llong_t result=a.to_long()<<shift;
  llong_t mask=
    true_size<(sizeof(llong_t)*8) ?
    (1LL << true_size) - 1 :
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
  PRECONDITION(a.is_long() && b.is_ulong());
  llong_t number=a.to_long();
  ullong_t shift=b.to_ulong();
  PRECONDITION(shift <= true_size);

  const llong_t sign = (1LL << (true_size - 1)) & number;
  const llong_t pad = (sign == 0) ? 0 : ~((1LL << (true_size - shift)) - 1);
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
  PRECONDITION(a.is_long() && b.is_ulong());
  PRECONDITION(b <= true_size || a == 0);

  ullong_t shift=b.to_ulong();
  llong_t result=a.to_long()<<shift;
  if(true_size<(sizeof(llong_t)*8))
  {
    const llong_t sign = (1LL << (true_size - 1)) & result;
    const llong_t mask = (1LL << true_size) - 1;
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
  PRECONDITION(a.is_long() && b.is_ulong());
  PRECONDITION(b <= true_size);

  ullong_t shift = b.to_ulong();
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
  PRECONDITION(a.is_ulong() && b.is_ulong());
  PRECONDITION(b <= true_size);

  ullong_t number=a.to_ulong();
  ullong_t shift=b.to_ulong();

  ullong_t revShift=true_size-shift;
  const ullong_t filter = 1ULL << (true_size - 1);
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
  PRECONDITION(a.is_ulong() && b.is_ulong());
  PRECONDITION(b <= true_size);

  ullong_t number=a.to_ulong();
  ullong_t shift=b.to_ulong();

  ullong_t revShift=true_size-shift;
  const ullong_t filter = 1ULL << (true_size - 1);
  ullong_t result=((number<<shift)&filter)|((number&filter) >> revShift);
  return result;
}
