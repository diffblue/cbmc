/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include "gcd.h"

/*******************************************************************\

Function: gcd

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer gcd(const mp_integer &_a, const mp_integer &_b)
{
  mp_integer a=_a, b=_b;

  if(a.is_negative()) a.negate();
  if(b.is_negative()) b.negate();

  if(a==1) return a;
  if(b==1) return b;
  if(a==b) return a;

  while(!b.is_zero())
  {
    mp_integer tmp_b=b;
    b=a%b;
    assert(b<tmp_b); // make progress
    a=tmp_b;
  }

  assert(!a.is_negative());

  return a;
}
