/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "fixedbv.h"

#include "std_types.h"
#include "std_expr.h"
#include "arith_tools.h"

fixedbv_spect::fixedbv_spect(const fixedbv_typet &type)
{
  integer_bits=type.get_integer_bits();
  width=type.get_width();
}

fixedbvt::fixedbvt(const constant_exprt &expr)
{
  from_expr(expr);
}

void fixedbvt::from_expr(const constant_exprt &expr)
{
  spec=fixedbv_spect(to_fixedbv_type(expr.type()));
  v = bv2integer(expr.get_value(), spec.width, true);
}

void fixedbvt::from_integer(const mp_integer &i)
{
  v=i*power(2, spec.get_fraction_bits());
}

mp_integer fixedbvt::to_integer() const
{
  // this rounds to zero, i.e., we just divide
  return v/power(2, spec.get_fraction_bits());
}

constant_exprt fixedbvt::to_expr() const
{
  fixedbv_typet type;
  type.set_width(spec.width);
  type.set_integer_bits(spec.integer_bits);
  PRECONDITION(spec.width != 0);
  return constant_exprt(integer2bv(v, spec.width), type);
}

void fixedbvt::round(const fixedbv_spect &dest_spec)
{
  std::size_t old_fraction_bits=spec.width-spec.integer_bits;
  std::size_t new_fraction_bits=dest_spec.width-dest_spec.integer_bits;

  mp_integer result;

  if(new_fraction_bits>old_fraction_bits)
    result=v*power(2, new_fraction_bits-old_fraction_bits);
  else if(new_fraction_bits<old_fraction_bits)
  {
    // may need to round
    mp_integer p=power(2, old_fraction_bits-new_fraction_bits);
    mp_integer div=v/p;
    mp_integer rem=v%p;
    if(rem<0)
      rem=-rem;

    if(rem*2>=p)
    {
      if(v<0)
        --div;
      else
        ++div;
    }

    result=div;
  }
  else // new_faction_bits==old_fraction_vits
  {
    // no change!
    result=v;
  }

  v=result;
  spec=dest_spec;
}

void fixedbvt::negate()
{
  v=-v;
}

fixedbvt &fixedbvt::operator*=(const fixedbvt &o)
{
  v*=o.v;

  fixedbv_spect old_spec=spec;

  spec.width+=o.spec.width;
  spec.integer_bits+=o.spec.integer_bits;

  round(old_spec);

  return *this;
}

fixedbvt &fixedbvt::operator+=(const fixedbvt &o)
{
  v += o.v;
  return *this;
}

fixedbvt &fixedbvt::operator-=(const fixedbvt &o)
{
  v -= o.v;
  return *this;
}

fixedbvt &fixedbvt::operator/=(const fixedbvt &o)
{
  v*=power(2, o.spec.get_fraction_bits());
  v/=o.v;

  return *this;
}

bool fixedbvt::operator==(int i) const
{
  return v==power(2, spec.get_fraction_bits())*i;
}

std::string fixedbvt::format(
  const format_spect &format_spec) const
{
  std::string dest;
  std::size_t fraction_bits=spec.get_fraction_bits();

  mp_integer int_value=v;
  mp_integer factor=power(2, fraction_bits);

  if(int_value.is_negative())
  {
    dest+='-';
    int_value.negate();
  }

  std::string base_10_string=
    integer2string(int_value*power(10, fraction_bits)/factor);

  while(base_10_string.size()<=fraction_bits)
    base_10_string="0"+base_10_string;

  std::string integer_part=
    std::string(base_10_string, 0, base_10_string.size()-fraction_bits);

  std::string fraction_part=
    std::string(base_10_string, base_10_string.size()-fraction_bits);

  dest+=integer_part;

  // strip trailing zeros
  while(!fraction_part.empty() &&
        fraction_part[fraction_part.size()-1]=='0')
    fraction_part.resize(fraction_part.size()-1);

  if(!fraction_part.empty())
    dest+="."+fraction_part;

  while(dest.size()<format_spec.min_width)
    dest=" "+dest;

  return dest;
}
