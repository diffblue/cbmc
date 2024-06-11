/*******************************************************************\

Module: Rational Numbers

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Rational Numbers

#include "rational_tools.h"

#include "arith_tools.h"
#include "mathematical_types.h"
#include "rational.h"

bool to_rational(const exprt &expr, rationalt &rational_value)
{
  if(!expr.is_constant())
    return true;

  std::string value = expr.get_string(ID_value);
  PRECONDITION(!value.empty());

  std::string no1, no2;
  char mode=0;

  bool is_negative = false;
  if(value[0] == '-')
  {
    is_negative = true;
    value = value.substr(1);
  }

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

  if(is_negative)
    rational_value = rationalt{-string2integer(no1)};
  else
    rational_value = rationalt{string2integer(no1)};

  switch(mode)
  {
  case 0:
    // do nothing
    break;

  case '.':
    DATA_INVARIANT(!no2.empty(), "decimal suffix should not be empty");
    if(no2 != "0")
    {
      DATA_INVARIANT(
        no2.back() != '0', "decimal suffix should not have trailing zeros");
      rational_value +=
        rationalt(string2integer(no2)) / rationalt(power(10, no2.size()));
    }
    break;

  case '/':
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
