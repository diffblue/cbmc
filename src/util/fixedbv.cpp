/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "std_types.h"
#include "fixedbv.h"
#include "arith_tools.h"

/*******************************************************************\

Function: fixedbv_spect::fixedbv_spect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

fixedbv_spect::fixedbv_spect(const fixedbv_typet &type)
{
  integer_bits=type.get_integer_bits();
  width=type.get_width();
}

/*******************************************************************\

Function: fixedbvt::fixedbvt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

fixedbvt::fixedbvt(const exprt &expr)
{
  from_expr(expr);
}

/*******************************************************************\

Function: fixedbvt::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fixedbvt::from_expr(const exprt &expr)
{
  spec=to_fixedbv_type(expr.type());
  v=binary2integer(id2string(expr.get(ID_value)), true);
}

/*******************************************************************\

Function: fixedbvt::from_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fixedbvt::from_integer(const mp_integer &i)
{
  v=i*power(2, spec.get_fraction_bits());
}

/*******************************************************************\

Function: fixedbvt::to_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer fixedbvt::to_integer() const
{
  // this rounds to zero, i.e., we just divide
  return v/power(2, spec.get_fraction_bits());
}

/*******************************************************************\

Function: fixedbvt::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt fixedbvt::to_expr() const
{
  fixedbv_typet type;
  type.set_width(spec.width);
  type.set_integer_bits(spec.integer_bits);
  exprt expr=exprt(ID_constant, type);
  assert(spec.width!=0);
  expr.set(ID_value, integer2binary(v, spec.width));
  return expr;
}

/*******************************************************************\

Function: fixedbvt::round

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fixedbvt::round(const fixedbv_spect &dest_spec)
{
  unsigned old_fraction_bits=spec.width-spec.integer_bits;
  unsigned new_fraction_bits=dest_spec.width-dest_spec.integer_bits;

  mp_integer result;

  if(new_fraction_bits>old_fraction_bits)
    result=v*power(2, new_fraction_bits-old_fraction_bits);
  else if(new_fraction_bits<old_fraction_bits)
  {
    // may need to round
    mp_integer p=power(2, old_fraction_bits-new_fraction_bits);
    mp_integer div=v/p;
    mp_integer rem=v%p;
    if(rem<0) rem=-rem;

    if(rem*2>=p)
    {
      if(v<0) --div; else ++div;
    }

    result=div;
  }

  v=result;
  spec=dest_spec;
}
  
/*******************************************************************\

Function: fixedbvt::negate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fixedbvt::negate()
{
  v=-v;
}

/*******************************************************************\

Function: fixedbvt::operator*

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

fixedbvt &fixedbvt::operator*=(const fixedbvt &o)
{
  v*=o.v;

  fixedbv_spect old_spec=spec;

  spec.width+=o.spec.width;
  spec.integer_bits+=o.spec.integer_bits;

  round(old_spec);

  return *this;
}

/*******************************************************************\

Function: fixedbvt::operator/=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

fixedbvt &fixedbvt::operator/=(const fixedbvt &o)
{
  v*=power(2, o.spec.get_fraction_bits());
  v/=o.v;

  return *this;
}

/*******************************************************************\

Function: fixedbvt::operator==

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool fixedbvt::operator==(int i) const
{
  return v==power(2, spec.get_fraction_bits())*i;
}

/*******************************************************************\

Function: fixedbvt::format

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string fixedbvt::format(
  const format_spect &format_spec) const
{
  std::string dest;
  unsigned fraction_bits=spec.get_fraction_bits();

  mp_integer int_value=v;
  mp_integer factor=power(2, fraction_bits);

  if(int_value.is_negative())
  {
    dest+="-";
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
