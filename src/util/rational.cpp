/*******************************************************************\

Module: Rational Numbers

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>

#include "rational.h"
#include "gcd.h"

/*******************************************************************\

Function: rationalt::operator+=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

rationalt &rationalt::operator+=(const rationalt &n)
{
  rationalt tmp(n);
  same_denominator(tmp);
  numerator+=tmp.numerator;
  normalize();
  return *this;
}

/*******************************************************************\

Function: rationalt::operator-=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

rationalt &rationalt::operator-=(const rationalt &n)
{
  rationalt tmp(n);
  same_denominator(tmp);
  numerator-=tmp.numerator;
  normalize();
  return *this;
}

/*******************************************************************\

Function: rationalt::operator*=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

rationalt &rationalt::operator*=(const rationalt &n)
{
  numerator*=n.numerator;
  denominator*=n.denominator;
  normalize();
  return *this;
}

/*******************************************************************\

Function: rationalt::operator/=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

rationalt &rationalt::operator/=(const rationalt &n)
{
  assert(!n.numerator.is_zero());
  numerator*=n.denominator;
  denominator*=n.numerator;
  normalize();
  return *this;
}

/*******************************************************************\

Function: rationalt::normalize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: rationalt::same_denominator

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rationalt::same_denominator(rationalt &n)
{
  if(denominator==n.denominator) return;

  numerator*=n.denominator;
  n.numerator*=denominator;

  mp_integer t=denominator*n.denominator;
  denominator=t;
  n.denominator=t;
}

/*******************************************************************\

Function: rationalt::invert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rationalt::invert()
{
  assert(numerator!=0);
  std::swap(numerator, denominator);
}

/*******************************************************************\

Function: inverse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

rationalt inverse(const rationalt &n)
{
  rationalt tmp(n);
  tmp.invert();
  return tmp;
}

/*******************************************************************\

Function: operator<<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream& operator<<(std::ostream& out, const rationalt &a)
{
  std::string d=integer2string(a.numerator);
  if(a.denominator!=1) d+="/"+integer2string(a.denominator);
  return out << d;
}
