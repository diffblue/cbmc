/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "bv_arithmetic.h"

#include <ostream>

#include "string2int.h"
#include "arith_tools.h"
#include "std_types.h"
#include "std_expr.h"

typet bv_spect::to_type() const
{
  if(is_signed)
    return signedbv_typet(width);
  return unsignedbv_typet(width);
}

mp_integer bv_spect::max_value() const
{
  return is_signed?power(2, width-1)-1:
                   power(2, width)-1;
}

mp_integer bv_spect::min_value() const
{
  return is_signed?-power(2, width-1):
                   0;
}

void bv_spect::from_type(const typet &type)
{
  if(type.id()==ID_unsignedbv)
    is_signed=false;
  else if(type.id()==ID_signedbv)
    is_signed=true;
  else
    UNREACHABLE;

  width = to_bitvector_type(type).get_width();
}

void bv_arithmetict::print(std::ostream &out) const
{
  out << to_ansi_c_string();
}

std::string bv_arithmetict::format(const format_spect &) const
{
  std::string result;

  result=integer2string(value);

  return result;
}

void bv_arithmetict::from_integer(const mp_integer &i)
{
  value=i;
  adjust();
}

void bv_arithmetict::adjust()
{
  mp_integer p=power(2, spec.width);
  value%=p;

  if(value>=p/2)
    value-=p;
}

mp_integer bv_arithmetict::pack() const
{
  if(value>=0)
    return value;
  return value+power(2, spec.width);
}

constant_exprt bv_arithmetict::to_expr() const
{
  return constant_exprt(integer2bvrep(value, spec.width), spec.to_type());
}

bv_arithmetict &bv_arithmetict::operator/=(const bv_arithmetict &other)
{
  PRECONDITION(other.spec == spec);

  if(other.value==0)
    value=0;
  else
    value/=other.value;

  return *this;
}

bv_arithmetict &bv_arithmetict::operator*=(const bv_arithmetict &other)
{
  PRECONDITION(other.spec == spec);

  value*=other.value;
  adjust();

  return *this;
}

bv_arithmetict &bv_arithmetict::operator+=(const bv_arithmetict &other)
{
  PRECONDITION(other.spec == spec);

  value+=other.value;
  adjust();

  return *this;
}

bv_arithmetict &bv_arithmetict::operator -= (const bv_arithmetict &other)
{
  PRECONDITION(other.spec == spec);

  value-=other.value;
  adjust();

  return *this;
}

bv_arithmetict &bv_arithmetict::operator%=(const bv_arithmetict &other)
{
  PRECONDITION(other.spec == spec);

  value%=other.value;
  adjust();

  return *this;
}

bool bv_arithmetict::operator<(const bv_arithmetict &other)
{
  return value<other.value;
}

bool bv_arithmetict::operator<=(const bv_arithmetict &other)
{
  return value<=other.value;
}

bool bv_arithmetict::operator>(const bv_arithmetict &other)
{
  return value>other.value;
}

bool bv_arithmetict::operator>=(const bv_arithmetict &other)
{
  return value>=other.value;
}

bool bv_arithmetict::operator==(const bv_arithmetict &other)
{
  return value==other.value;
}

bool bv_arithmetict::operator==(int i)
{
  return value==i;
}

bool bv_arithmetict::operator!=(const bv_arithmetict &other)
{
  return value!=other.value;
}

void bv_arithmetict::change_spec(const bv_spect &dest_spec)
{
  spec=dest_spec;
  adjust();
}

void bv_arithmetict::from_expr(const constant_exprt &expr)
{
  spec=bv_spect(expr.type());
  value = bvrep2integer(expr.get_value(), spec.width, spec.is_signed);
}
