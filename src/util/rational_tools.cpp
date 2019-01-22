/*******************************************************************\

Module: Rational Numbers

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Rational Numbers

#include "rational_tools.h"

#include "mathematical_types.h"
#include "rational.h"

static mp_integer power10(size_t i)
{
  mp_integer result=1;

  for(; i!=0; i--)
    result*=10;

  return result;
}

bool to_rational(const exprt &expr, rationalt &rational_value)
{
  if(expr.id()!=ID_constant)
    return true;

  const std::string &value=expr.get_string(ID_value);

  std::string no1, no2;
  char mode=0;

  for(const char ch : value)
  {
    if(isdigit(ch))
    {
      if(mode==0)
        no1+=ch;
      else
        no2+=ch;
    }
    else if(ch=='/' || ch=='.')
    {
      if(mode==0)
        mode=ch;
      else
        return true;
    }
    else
      return true;
  }

  switch(mode)
  {
  case 0:
    rational_value=rationalt(string2integer(no1));
    break;

  case '.':
    rational_value=rationalt(string2integer(no1));
    rational_value+=
      rationalt(string2integer(no2))/rationalt(power10(no2.size()));
    break;

  case '/':
    rational_value=rationalt(string2integer(no1));
    rational_value/=rationalt(string2integer(no2));
    break;

  default:
    return true;
  }

  return false;
}

constant_exprt from_rational(const rationalt &a)
{
  std::string d=integer2string(a.get_numerator());
  if(a.get_denominator()!=1)
    d+="/"+integer2string(a.get_denominator());
  return constant_exprt(d, rational_typet());
}
