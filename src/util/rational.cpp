/*******************************************************************\

Module: Rational Numbers

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Rational Numbers

#include "rational.h"

#include <algorithm>
#include <ostream>

#include "invariant.h"

rationalt &rationalt::operator+=(const rationalt &n)
{
  rationalt tmp(n);
  same_denominator(tmp);
  numerator+=tmp.numerator;
  normalize();
  return *this;
}

rationalt &rationalt::operator-=(const rationalt &n)
{
  rationalt tmp(n);
  same_denominator(tmp);
  numerator-=tmp.numerator;
  normalize();
  return *this;
}

rationalt &rationalt::operator-()
{
  numerator.negate();
  return *this;
}

rationalt &rationalt::operator*=(const rationalt &n)
{
  numerator*=n.numerator;
  denominator*=n.denominator;
  normalize();
  return *this;
}

rationalt &rationalt::operator/=(const rationalt &n)
{
  PRECONDITION(!n.numerator.is_zero());
  numerator*=n.denominator;
  denominator*=n.numerator;
  normalize();
  return *this;
}

void rationalt::normalize()
{
  // first do sign

  if(denominator.is_negative())
  {
    denominator.negate();
    numerator.negate();
  }

  // divide by gcd

  mp_integer _gcd=gcd(denominator, numerator);
  if(_gcd!=1 && !_gcd.is_zero())
  {
    denominator/=_gcd;
    numerator/=_gcd;
  }
}

void rationalt::same_denominator(rationalt &n)
{
  if(denominator==n.denominator)
    return;

  numerator*=n.denominator;
  n.numerator*=denominator;

  mp_integer t=denominator*n.denominator;
  denominator=t;
  n.denominator=t;
}

void rationalt::invert()
{
  PRECONDITION(numerator != 0);
  std::swap(numerator, denominator);
}

rationalt inverse(const rationalt &n)
{
  rationalt tmp(n);
  tmp.invert();
  return tmp;
}

std::ostream &operator<<(std::ostream &out, const rationalt &a)
{
  std::string d=integer2string(a.get_numerator());
  if(a.get_denominator()!=1)
    d+="/"+integer2string(a.get_denominator());
  return out << d;
}
