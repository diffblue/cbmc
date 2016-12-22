/*******************************************************************\

Module: Rational Numbers

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "rational.h"
#include "std_types.h"

#include "rational_tools.h"

/*******************************************************************\

Function: power10

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static mp_integer power10(size_t i)
{
  mp_integer result=1;

  for(; i!=0; i--)
    result*=10;

  return result;
}

/*******************************************************************\

Function: to_rational

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool to_rational(const exprt &expr, rationalt &rational_value)
{
  if(expr.id()!=ID_constant) return true;

  const std::string &value=expr.get_string(ID_value);

  std::string no1, no2;
  char mode=0;

  for(std::string::const_iterator it=value.begin();
      it!=value.end();
      ++it)
  {
    const char ch=*it;

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

/*******************************************************************\

Function: from_rational

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt from_rational(const rationalt &a)
{
  std::string d=integer2string(a.get_numerator());
  if(a.get_denominator()!=1)
    d+="/"+integer2string(a.get_denominator());
  constant_exprt result;
  result.type()=rational_typet();
  result.set_value(d);
  return result;
}
