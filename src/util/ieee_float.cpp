/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stdint.h>

#include <cassert>
#include <cmath>
#include <limits>

#include "arith_tools.h"
#include "std_types.h"
#include "std_expr.h"
#include "ieee_float.h"

/*******************************************************************\

Function: ieee_float_spect::bias

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer ieee_float_spect::bias() const
{
  return power(2, e-1)-1;
}

/*******************************************************************\

Function: ieee_float_spect::to_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

floatbv_typet ieee_float_spect::to_type() const
{
  floatbv_typet result;
  result.set_f(f);
  result.set_width(width());
  return result;
}

/*******************************************************************\

Function: ieee_float_spect::max_exponent

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer ieee_float_spect::max_exponent() const
{
  return power(2, e)-1;
}

/*******************************************************************\

Function: ieee_float_spect::max_fraction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer ieee_float_spect::max_fraction() const
{
  return power(2, f)-1;
}

/*******************************************************************\

Function: ieee_float_spect::from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_float_spect::from_type(const floatbv_typet &type)
{
  unsigned width=type.get_width();
  f=type.get_f();
  assert(f!=0);
  assert(f<width);
  e=width-f-1;
}

/*******************************************************************\

Function: ieee_floatt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_floatt::print(std::ostream &out) const
{
  out << to_ansi_c_string();
}

/*******************************************************************\

Function: ieee_floatt::format

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string ieee_floatt::format(const format_spect &format_spec) const
{
  std::string result;

  if(sign_flag) result+="-";
  
  if((NaN_flag || infinity_flag) && !sign_flag) result+="+";

  // special cases
  if(NaN_flag)
    result+="NaN";
  else if(infinity_flag)
    result+="inf";
  else if(is_zero())
  {
    result+="0";

    // add zeros, if needed
    if(format_spec.precision>0)
    {
      result+='.';
      for(unsigned i=0; i<format_spec.precision; i++)
        result+='0';
    }
  }
  else
  {
    mp_integer _exponent, _fraction;
    extract(_fraction, _exponent);

    // convert to base 10
    if(_exponent>=0)
    {
      result+=integer2string(_fraction*power(2, _exponent));
      
      // add zeros, if needed
      if(format_spec.precision>0)
      {
        result+='.';
        for(unsigned i=0; i<format_spec.precision; i++)
          result+='0';
      }
    }
    else
    {
      #if 1
      mp_integer position=-_exponent;

      // 10/2=5 -- this makes it base 10
      _fraction*=power(5, position);

      // apply rounding
      if(position>format_spec.precision)
      {
        mp_integer r=power(10, position-format_spec.precision);
        mp_integer remainder=_fraction%r;
        _fraction/=r;
        // not sure if this is the right kind of rounding here
        if(remainder>=r/2) ++_fraction;
        position=format_spec.precision;
      }

      std::string tmp=integer2string(_fraction);

      // pad with zeros from the front, if needed
      while(mp_integer(tmp.size())<=position) tmp="0"+tmp;

      unsigned dot=tmp.size()-integer2long(position);
      result+=std::string(tmp, 0, dot)+'.';
      result+=std::string(tmp, dot, std::string::npos);

      // append zeros if needed
      for(mp_integer i=position; i<format_spec.precision; ++i)
        result+='0';
      #else

      result+=integer2string(_fraction);

      if(_exponent!=0)
        result+="*2^"+integer2string(_exponent);

      #endif
    }
  }

  while(result.size()<format_spec.min_width)
    result=" "+result;

  return result;
}

/*******************************************************************\

Function: ieee_floatt::unpack

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_floatt::unpack(const mp_integer &i)
{
  assert(spec.f!=0);
  assert(spec.e!=0);

  {
    mp_integer tmp=i;

    // split this apart
    mp_integer pf=power(2, spec.f);
    fraction=tmp%pf;
    tmp/=pf;

    mp_integer pe=power(2, spec.e);
    exponent=tmp%pe;
    tmp/=pe;

    sign_flag=(tmp!=0);
  }

  // NaN?
  if(exponent==spec.max_exponent() && fraction!=0)
  {
    make_NaN();
  }
  else if(exponent==spec.max_exponent() && fraction==0) // Infinity
  {
    NaN_flag=false;
    infinity_flag=true;
  }
  else if(exponent==0 && fraction==0) // zero
  {
    NaN_flag=false;
    infinity_flag=false;
  }
  else if(exponent==0) // denormal?
  {
    NaN_flag=false;
    infinity_flag=false;
    exponent=-spec.bias()+1; // NOT -spec.bias()!
  }
  else // normal
  {
    NaN_flag=false;
    infinity_flag=false;
    fraction+=power(2, spec.f); // hidden bit!    
    exponent-=spec.bias(); // un-bias
  }
}

/*******************************************************************\

Function: ieee_floatt::pack

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer ieee_floatt::pack() const
{
  mp_integer result=0;

  // sign bit
  if(sign_flag) result+=power(2, spec.e+spec.f);

  if(NaN_flag)
  {
    result+=power(2, spec.f)*spec.max_exponent();
    result+=1;
  }
  else if(infinity_flag)
  {
    result+=power(2, spec.f)*spec.max_exponent();
  }
  else if(fraction==0 && exponent==0)
  {
  }
  else if(fraction>=power(2, spec.f)) // normal?
  {
    // fraction -- need to hide hidden bit
    result+=fraction-power(2, spec.f); // hidden bit

    // exponent -- bias!
    result+=power(2, spec.f)*(exponent+spec.bias());
  }
  else // denormal
  {
    result+=fraction; // denormal -- no hidden bit
    // the exponent is zero
  }

  return result;
}

/*******************************************************************\

Function: ieee_floatt::extract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_floatt::extract(
  mp_integer &_fraction,
  mp_integer &_exponent) const
{
  if(is_zero() || is_NaN() || is_infinity())
  {
    _fraction=_exponent=0;
    return;
  }

  _exponent=exponent;
  _fraction=fraction;

  // adjust exponent
  _exponent-=spec.f;

  // try to integer-ize
  while((_fraction%2)==0)
  {
    _fraction/=2;
    ++_exponent;
  }
}

/*******************************************************************\

Function: ieee_floatt::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_floatt::build(
  const mp_integer &_fraction,
  const mp_integer &_exponent)
{
  sign_flag=_fraction<0;
  fraction=_fraction;
  if(sign_flag) fraction=-fraction;
  exponent=_exponent;
  exponent+=spec.f;
  align();
}

/*******************************************************************\

Function: ieee_floatt::from_base10

  Inputs:

 Outputs:

 Purpose: compute f * (10^e)

\*******************************************************************/

void ieee_floatt::from_base10(
  const mp_integer &_fraction,
  const mp_integer &_exponent)
{
  NaN_flag=infinity_flag=false;
  sign_flag=_fraction<0;
  fraction=_fraction;
  if(sign_flag) fraction=-fraction;
  exponent=spec.f;
  exponent+=_exponent;
  
  if(_exponent<0)
  {
    // bring to max. precision
    mp_integer e_power=power(2, spec.e);
    fraction*=power(2, e_power);
    exponent-=e_power;
    fraction/=power(5, -_exponent);
  }
  else if(_exponent>0)
  {
    // fix base
    fraction*=power(5, _exponent);
  }
  
  align();
}

/*******************************************************************\

Function: ieee_floatt::from_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_floatt::from_integer(const mp_integer &i)
{
  NaN_flag=infinity_flag=sign_flag=false;
  exponent=spec.f;
  fraction=i;
  align();
}

/*******************************************************************\

Function: ieee_floatt::align

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_floatt::align()
{
  // NaN?
  if(NaN_flag)
  {
    fraction=0;
    exponent=0;
    sign_flag=false;
    return;
  }

  // do sign
  if(fraction<0)
  {
    sign_flag=!sign_flag;
    fraction=-fraction;
  }

  // zero?
  if(fraction==0)
  {
    exponent=0;
    return;
  }

  // 'usual case'

  mp_integer f_power=power(2, spec.f);
  mp_integer f_power_next=power(2, spec.f+1);

  mp_integer exponent_offset=0;

  if(fraction<f_power) // too small?
  {
    mp_integer tmp_fraction=fraction;

    while(tmp_fraction<f_power)
    {
      tmp_fraction*=2;
      --exponent_offset;
    }
  }
  else if(fraction>=f_power_next) // too big?
  {
    mp_integer tmp_fraction=fraction;

    while(tmp_fraction>=f_power_next)
    {
      tmp_fraction/=2;
      ++exponent_offset;
    }
  }

  mp_integer biased_exponent=exponent+exponent_offset+spec.bias();

  // exponent too large (infinity)?
  if(biased_exponent>=spec.max_exponent())
    infinity_flag=true;
  else if(biased_exponent<=0) // exponent too small?
  {
    // produce a denormal (or zero)
    mp_integer new_exponent=mp_integer(1)-spec.bias();
    exponent_offset=new_exponent-exponent;
  }

  exponent+=exponent_offset;

  if(exponent_offset>0)
  {
    divide_and_round(fraction, power(2, exponent_offset));

    // rounding might make the fraction too big!
    if(fraction==f_power_next)
    {
      fraction=f_power;
      ++exponent;
    }
  }
  else if(exponent_offset<0)
    fraction*=power(2, -exponent_offset);

  if(fraction==0)
    exponent=0;
}

/*******************************************************************\

Function: ieee_floatt::divide_and_round

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_floatt::divide_and_round(
  mp_integer &fraction,
  const mp_integer &factor)
{
  mp_integer remainder=fraction%factor;
  fraction/=factor;

  if(remainder!=0)
  {
    switch(rounding_mode)
    {
    case ROUND_TO_EVEN:
      {
        mp_integer factor_middle=factor/2;
        if(remainder<factor_middle)
        {
          // crop
        }
        else if(remainder>factor_middle)
        {
          ++fraction;
        }
        else // exactly in the middle -- go to even
        {
          if((fraction%2)!=0)
            ++fraction;
        }
      }
      break;

    case ROUND_TO_ZERO:
      // this means just crop
      break;

    case ROUND_TO_MINUS_INF:
      if(sign_flag)
        ++fraction;
      break;

    case ROUND_TO_PLUS_INF:
      if(!sign_flag)
        ++fraction;
      break;

    default:
      assert(false);
    }
  }
}

/*******************************************************************\

Function: ieee_floatt::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

constant_exprt ieee_floatt::to_expr() const
{
  constant_exprt result(spec.to_type());
  result.set_value(integer2binary(pack(), spec.width()));
  return result;
}

/*******************************************************************\

Function: operator /=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ieee_floatt &ieee_floatt::operator /= (const ieee_floatt &other)
{
  assert(other.spec.f==spec.f);
  
  // NaN/x = NaN
  if(NaN_flag) return *this;
  
  // x/NaN = NaN
  if(other.NaN_flag) { make_NaN(); return *this; }
  
  // 0/0 = NaN
  if(is_zero() && other.is_zero()) { make_NaN(); return *this; }

  // x/0 = +-inf
  if(other.is_zero())
  {
    infinity_flag=true;
    if(other.sign_flag) negate();
    return *this;
  }
  
  // x/inf = NaN
  if(other.infinity_flag)
  {
    if(infinity_flag) { make_NaN(); return *this; }

    bool old_sign = sign_flag;
    make_zero();
    sign_flag = old_sign;

    if(other.sign_flag)
      negate();

    return *this;
  } // inf/x = inf
  else if(infinity_flag)
  {
    if(other.sign_flag) negate();

    return *this;
  }

  exponent-=other.exponent;
  fraction*=power(2, spec.f);

  // to account for error
  fraction*=power(2, spec.f);
  exponent-=spec.f;

  fraction/=other.fraction;

  if(other.sign_flag) negate();

  align();

  return *this;
}

/*******************************************************************\

Function: operator *=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ieee_floatt &ieee_floatt::operator *= (const ieee_floatt &other)
{
  assert(other.spec.f==spec.f);
  
  if(other.NaN_flag) make_NaN();
  if(NaN_flag) return *this;
  
  if(infinity_flag || other.infinity_flag)
  {
    if(is_zero() || other.is_zero())
    {
      // special case Inf * 0 is NaN
      make_NaN();
      return *this;
    }

    if(other.sign_flag) negate();
    infinity_flag=true;
    return *this;
  }

  exponent+=other.exponent;
  exponent-=spec.f;
  fraction*=other.fraction;

  if(other.sign_flag) negate();

  align();

  return *this;
}

/*******************************************************************\

Function: operator +=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ieee_floatt &ieee_floatt::operator += (const ieee_floatt &other)
{
  ieee_floatt _other=other;

  assert(_other.spec==spec);
  
  if(other.NaN_flag) make_NaN();
  if(NaN_flag) return *this;

  if(infinity_flag && other.infinity_flag)
  {
    if(sign_flag==other.sign_flag) return *this;
    make_NaN();
    return *this;
  }
  else if(infinity_flag)
    return *this;
  else if(other.infinity_flag)
  {
    infinity_flag=true;
    sign_flag=other.sign_flag;
    return *this;
  }

  if(is_zero() && other.is_zero())
  { 
    if(get_sign() == other.get_sign())
      return *this;
    else 
    {
      if(rounding_mode == ROUND_TO_MINUS_INF)
      {
        set_sign(true);
        return *this;      
      } 
      else
      {
        set_sign(false);
        return *this;
      }
    }
  }
  
  // get smaller exponent
  if(_other.exponent<exponent)
  {
    fraction*=power(2, exponent-_other.exponent);
    exponent=_other.exponent;
  }
  else if(exponent<_other.exponent)
  {
    _other.fraction*=power(2, _other.exponent-exponent);
    _other.exponent=exponent;
  }
  
  assert(exponent==_other.exponent);

  if(sign_flag) fraction.negate();
  if(_other.sign_flag) _other.fraction.negate();
  
  fraction+=_other.fraction;
  
  // on zero, retain original sign
  if(fraction!=0)
  {
    sign_flag=(fraction<0);
    if(sign_flag) fraction.negate();
  }

  align();

  return *this;
}

/*******************************************************************\

Function: operator -=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ieee_floatt &ieee_floatt::operator -= (const ieee_floatt &other)
{
  ieee_floatt _other=other;
  _other.sign_flag=!_other.sign_flag;
  return (*this)+=_other;
}

/*******************************************************************\

Function: operator <

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator < (const ieee_floatt &a, const ieee_floatt &b)
{
  if(a.NaN_flag || b.NaN_flag) return false;

  // check both zero?
  if(a.is_zero() && b.is_zero())
    return false;

  // one of them zero?
  if(a.is_zero())
    return !b.sign_flag;
  else if(b.is_zero())
    return a.sign_flag;

  // check sign
  if(a.sign_flag!=b.sign_flag)
    return a.sign_flag;
   
  // handle infinity
  if(a.infinity_flag)
  {
    if(b.infinity_flag)
      return false;
    else
      return a.sign_flag; 
  }
  else if(b.infinity_flag)
    return !a.sign_flag;

  // check exponent
  if(a.exponent!=b.exponent)
  {
    if(a.sign_flag) // both negative
      return a.exponent>b.exponent;
    else
      return a.exponent<b.exponent;
  }
  
  // check significand
  if(a.sign_flag) // both negative
    return a.fraction>b.fraction;
  else
    return a.fraction<b.fraction;
}

/*******************************************************************\

Function: operator <=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator <=(const ieee_floatt &a, const ieee_floatt &b)
{
  if(a.NaN_flag || b.NaN_flag) return false;
  
  // check zero
  if(a.is_zero() && b.is_zero())
    return true;

  // handle infinity
  if(a.infinity_flag && b.infinity_flag && a.sign_flag==b.sign_flag)
    return true;
  
  if(!a.infinity_flag && !b.infinity_flag &&
     a.sign_flag==b.sign_flag &&
     a.exponent==b.exponent &&
     a.fraction==b.fraction)
    return true;
    
  return a<b;
}

/*******************************************************************\

Function: operator >

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator > (const ieee_floatt &a, const ieee_floatt &b)
{
  return b < a;
}

/*******************************************************************\

Function: operator >=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator >=(const ieee_floatt &a, const ieee_floatt &b)
{
  return b <= a;
}

/*******************************************************************\

Function: operator ==

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator ==(const ieee_floatt &a, const ieee_floatt &b)
{
  // packed equality!
  if(a.NaN_flag && b.NaN_flag)
    return true;
  else if(a.NaN_flag || b.NaN_flag)
    return false;

  if(a.infinity_flag && b.infinity_flag &&
     a.sign_flag == b.sign_flag) return true;
  else if(a.infinity_flag || b.infinity_flag)
    return false;

  //if(a.is_zero() && b.is_zero()) return true;

  return a.exponent==b.exponent &&
         a.fraction==b.fraction &&
         a.sign_flag==b.sign_flag;
}

/*******************************************************************\

Function: ieee_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ieee_equal(const ieee_floatt &a, const ieee_floatt &b)
{
  if(a.NaN_flag || b.NaN_flag) return false;
  if(a.is_zero() && b.is_zero()) return true;
  assert(a.spec==b.spec);
  return a==b;
}

/*******************************************************************\

Function: operator ==

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator ==(const ieee_floatt &a, int i)
{
  ieee_floatt other;
  other.spec=a.spec;
  other.from_integer(i);
  return a==other;
}

/*******************************************************************\

Function: operator !=

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator !=(const ieee_floatt &a, const ieee_floatt &b)
{
  return !(a==b);
}

/*******************************************************************\

Function: ieee_not_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ieee_not_equal(const ieee_floatt &a, const ieee_floatt &b)
{
  if(a.NaN_flag || b.NaN_flag) return true; // !!!
  if(a.is_zero() && b.is_zero()) return false;
  assert(a.spec==b.spec);
  return a!=b;
}

/*******************************************************************\

Function: ieee_floatt::change_spec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_floatt::change_spec(const ieee_float_spect &dest_spec)
{
  mp_integer _exponent=exponent-spec.f;
  mp_integer _fraction=fraction;
  
  bool old_sign = sign_flag;
  if(sign_flag) _fraction.negate();

  spec=dest_spec;
  build(_fraction, _exponent);

  if(old_sign && !sign_flag) //this can happen if fraction == 0
  {
    assert(fraction == 0);
    negate();
  }
}

/*******************************************************************\

Function: ieee_floatt::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_floatt::from_expr(const constant_exprt &expr)
{
  spec=to_floatbv_type(expr.type());
  unpack(binary2integer(id2string(expr.get_value()), false));
}

/*******************************************************************\

Function: ieee_floatt::to_integer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer ieee_floatt::to_integer() const
{
  if(NaN_flag || infinity_flag || is_zero()) return 0;

  mp_integer result=fraction;

  mp_integer new_exponent=exponent-spec.f;
  
  // if the exponent is negative, divide
  if(new_exponent<0)
    result/=power(2, -new_exponent);
  else  
    result*=power(2, new_exponent); // otherwise, multiply

  if(sign_flag)
    result.negate();
    
  return result;
}

/*******************************************************************\

Function: ieee_floatt::from_double

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_floatt::from_double(const double d)
{
  spec.f=52;
  spec.e=11;
  assert(spec.width()==64);

  // we need a 64-bit integer type for this  
  assert(sizeof(double)==sizeof(long long unsigned int));
  
  union
  {
    double d;
    long long unsigned int i;
  } u;
  
  u.d=d;
  
  unpack(u.i);
}

/*******************************************************************\

Function: ieee_floatt::from_float

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_floatt::from_float(const float f)
{
  spec.f=23;
  spec.e=8;
  assert(spec.width()==32);
  
  assert(sizeof(float)==sizeof(unsigned int));

  union
  {
    float f;
    unsigned int i;
  } u;
  
  u.f=f;

  unpack(u.i);
}

/*******************************************************************\

Function: ieee_floatt::make_NaN

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_floatt::make_NaN()
{
  NaN_flag=true;
  //sign=false;
  exponent=0;
  fraction=0;
  infinity_flag=false;
}

/*******************************************************************\

Function: ieee_floatt::make_fltmax

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_floatt::make_fltmax()
{
  mp_integer bit_pattern = power(2,spec.e + spec.f)-1 - power(2,spec.f);
  unpack(bit_pattern);
}

/*******************************************************************\

Function: ieee_floatt::make_fltmin

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_floatt::make_fltmin()
{
  unpack(power(2,spec.f));
}

/*******************************************************************\

Function: ieee_floatt::make_plus_infinity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_floatt::make_plus_infinity()
{
  NaN_flag=false;
  sign_flag=false;
  exponent=0;
  fraction=0;
  infinity_flag=true;
}

/*******************************************************************\

Function: ieee_floatt::make_minus_infinity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ieee_floatt::make_minus_infinity()
{
  make_plus_infinity();
  sign_flag=true;
}

/*******************************************************************\

Function: ieee_floatt::is_double

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

bool ieee_floatt::is_double() const
{
  return spec.f == 52 && spec.e == 11;
} 

/*******************************************************************\

Function: ieee_floatt::is_float

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

bool ieee_floatt::is_float() const
{
  return spec.f == 23 && spec.e == 8;
}

/*******************************************************************\

Function: ieee_floatt::to_double
 
  Inputs:

 Outputs:

 Purpose: Note that calling from_double -> to_double can return different bit
          patterns for NaN.

\*******************************************************************/

double ieee_floatt::to_double() const
{
  union { double f; uint64_t i; } a;

  if(infinity_flag)
  {
    if(sign_flag) 
      return -std::numeric_limits<double>::infinity();
    else
      return std::numeric_limits<double>::infinity();
  }

  if(NaN_flag)
  {
    if(sign_flag) 
      return -std::numeric_limits<double>::quiet_NaN();
    else
      return std::numeric_limits<double>::quiet_NaN();
  }

  mp_integer i = pack();
  assert(i.is_ulong());
  
  a.i = i.to_ulong();
  return a.f;
}

/*******************************************************************\

Function: ieee_floatt:to_float
 
  Inputs:

 Outputs:

 Purpose: Note that calling from_float -> to_float can return different bit
          patterns for NaN.

\*******************************************************************/

float ieee_floatt::to_float() const
{
  if(sizeof(unsigned) != sizeof(float))
  {
    throw "ieee_floatt::to_float not supported on this architecture";
  }

  union { float f; uint32_t i; } a;

  if(infinity_flag)
  {
    if(sign_flag) 
      return -std::numeric_limits<float>::infinity();
    else
      return std::numeric_limits<float>::infinity();
  }

  if(NaN_flag)
  {
    if(sign_flag) 
      return -std::numeric_limits<float>::quiet_NaN();
    else
      return std::numeric_limits<float>::quiet_NaN();
  }

  mp_integer i = pack();
  assert(i.is_ulong());
    
  a.i = (unsigned) i.to_ulong();
  return a.f;
}

/*******************************************************************\

Function: ieee_floatt::next_representable
 
  Inputs: 

 Outputs:

 Purpose: Sets *this to the next representable number closer to 
          plus infinity (greater = true) or minus infinity 
          (greater = false).

\*******************************************************************/

void ieee_floatt::next_representable(bool greater)
{
  if(is_NaN())
    return;
  
  bool old_sign = get_sign();

  if(is_zero())
  {
    unpack(1);
    set_sign(!greater);

    return;
  }

  if(is_infinity())
  {
    if(get_sign() == greater)
    {
      make_fltmax();
      set_sign(old_sign);
    } 
    return;
  }
  
  bool dir;
  if(greater)
  {
    if(get_sign())
      dir = false;
    else
      dir = true;
  } 
  else
  {
    if(get_sign())
      dir = true;
    else
      dir = false;
  }

  set_sign(false);

  mp_integer old = pack();
  if(dir)
    ++old;
  else
    --old;

  unpack(old);

  //sign change impossible (zero case caught earler)
  set_sign(old_sign);

  //mp_integer new_exp = exponent;
  //mp_integer new_frac = fraction + dir;

  //std::cout << exponent << ":" << fraction << std::endl;
  //std::cout << new_exp << ":" << new_frac << std::endl;
  
  //if(get_sign())
  //  new_frac.negate();

  //new_exp -= spec.f;
  //build(new_frac, new_exp);
}

