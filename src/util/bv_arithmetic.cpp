/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <cstdlib>

#include "arith_tools.h"
#include "std_types.h"
#include "std_expr.h"
#include "bv_arithmetic.h"

/*******************************************************************\

Function: bv_spect::to_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet bv_spect::to_type() const
{
  if(is_signed) return signedbv_typet(width);
  return unsignedbv_typet(width);
}

/*******************************************************************\

Function: bv_spect::max_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer bv_spect::max_value() const
{
  return is_signed?power(2, width-1)-1:
                   power(2, width)-1;
}

/*******************************************************************\

Function: bv_spect::min_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer bv_spect::min_value() const
{
  return is_signed?-power(2, width-1):
                   0;
}

/*******************************************************************\

Function: bv_spect::from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_spect::from_type(const typet &type)
{
  if(type.id()==ID_unsignedbv)
    is_signed=false;
  else if(type.id()==ID_signedbv)
    is_signed=true;
  else
    assert(0);
  
  width=atoi(type.get(ID_width).c_str());
}

/*******************************************************************\

Function: bv_arithmetict::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_arithmetict::print(std::ostream &out) const
{
  out << to_ansi_c_string();
}

/*******************************************************************\

Function: bv_arithmetict::format

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string bv_arithmetict::format(const format_spect &format_spec) const
{
  std::string result;

  result=integer2string(value);

  return result;
}

/*******************************************************************\

Function: bv_arithmetict::from_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_arithmetict::from_integer(const mp_integer &i)
{
  value=i;
  adjust();
}

/*******************************************************************\

Function: bv_arithmetict::adjust

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_arithmetict::adjust()
{
  mp_integer p=power(2, spec.width);
  value%=p;

  if(value>=p/2)
    value-=p;
}

/*******************************************************************\

Function: bv_arithmetict::pack

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer bv_arithmetict::pack() const
{
  if(value>=0) return value;
  return value+power(2, spec.width);
}

/*******************************************************************\

Function: bv_arithmetict::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt bv_arithmetict::to_expr() const
{
  constant_exprt result(spec.to_type());
  result.set_value(integer2binary(value, spec.width));
  return result;
}

/*******************************************************************\

Function: operator /=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bv_arithmetict &bv_arithmetict::operator /= (const bv_arithmetict &other)
{
  assert(other.spec==spec);

  if(other.value==0)
    value=0;
  else
    value/=other.value;  

  return *this;
}

/*******************************************************************\

Function: operator *=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bv_arithmetict &bv_arithmetict::operator *= (const bv_arithmetict &other)
{
  assert(other.spec==spec);
  
  value*=other.value;
  adjust();
  
  return *this;
}

/*******************************************************************\

Function: operator +=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bv_arithmetict &bv_arithmetict::operator += (const bv_arithmetict &other)
{
  assert(other.spec==spec);

  value+=other.value;
  adjust();

  return *this;
}

/*******************************************************************\

Function: operator -=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bv_arithmetict &bv_arithmetict::operator -= (const bv_arithmetict &other)
{
  assert(other.spec==spec);

  value-=other.value;
  adjust();

  return *this;
}

/*******************************************************************\

Function: operator %=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bv_arithmetict &bv_arithmetict::operator %= (const bv_arithmetict &other)
{
  assert(other.spec==spec);

  value%=other.value;
  adjust();

  return *this;
}

/*******************************************************************\

Function: operator <

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator < (const bv_arithmetict &a, const bv_arithmetict &b)
{
  return a.value<b.value;
}

/*******************************************************************\

Function: operator <=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator <=(const bv_arithmetict &a, const bv_arithmetict &b)
{
  return a.value<=b.value;
}

/*******************************************************************\

Function: operator >

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator > (const bv_arithmetict &a, const bv_arithmetict &b)
{
  return a.value>b.value;
}

/*******************************************************************\

Function: operator >=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator >=(const bv_arithmetict &a, const bv_arithmetict &b)
{
  return a.value>=b.value;
}

/*******************************************************************\

Function: operator ==

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator ==(const bv_arithmetict &a, const bv_arithmetict &b)
{
  return a.value==b.value;
}

/*******************************************************************\

Function: operator ==

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator ==(const bv_arithmetict &a, int i)
{
  return a.value==i;
}

/*******************************************************************\

Function: operator !=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator !=(const bv_arithmetict &a, const bv_arithmetict &b)
{
  return a.value!=b.value;
}

/*******************************************************************\

Function: bv_arithmetict::change_spec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_arithmetict::change_spec(const bv_spect &dest_spec)
{
  spec=dest_spec;
  adjust();
}

/*******************************************************************\

Function: bv_arithmetict::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_arithmetict::from_expr(const exprt &expr)
{
  assert(expr.is_constant());
  spec=expr.type();
  value=binary2integer(expr.get_string(ID_value), spec.is_signed);
}
