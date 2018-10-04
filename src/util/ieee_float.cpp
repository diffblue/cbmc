/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ieee_float.h"

#include <cstdint>
#include <ostream>
#include <cmath>
#include <limits>

#include "arith_tools.h"
#include "invariant.h"
#include "std_expr.h"
#include "std_types.h"

mp_integer ieee_float_spect::bias() const
{
  return power(2, e-1)-1;
}

floatbv_typet ieee_float_spect::to_type() const
{
  floatbv_typet result;
  result.set_f(f);
  result.set_width(width());
  if(x86_extended)
    result.set(ID_x86_extended, true);
  return result;
}

mp_integer ieee_float_spect::max_exponent() const
{
  return power(2, e)-1;
}

mp_integer ieee_float_spect::max_fraction() const
{
  return power(2, f)-1;
}

void ieee_float_spect::from_type(const floatbv_typet &type)
{
  std::size_t width=type.get_width();
  f=type.get_f();
  DATA_INVARIANT(f != 0, "mantissa must be at least 1 bit");
  DATA_INVARIANT(
    f < width,
    "mantissa bits must be less than "
    "originating type width");
  e=width-f-1;
  x86_extended=type.get_bool(ID_x86_extended);
  if(x86_extended)
    e=e-1; // no hidden bit
}

void ieee_floatt::print(std::ostream &out) const
{
  out << to_ansi_c_string();
}

std::string ieee_floatt::format(const format_spect &format_spec) const
{
  std::string result;

  switch(format_spec.style)
  {
  case format_spect::stylet::DECIMAL:
    result+=to_string_decimal(format_spec.precision);
    break;

  case format_spect::stylet::SCIENTIFIC:
    result+=to_string_scientific(format_spec.precision);
    break;

  case format_spect::stylet::AUTOMATIC:
    {
      // On Linux, the man page says:
      // "Style e is used if the exponent from its conversion
      //  is less than -4 or greater than or equal to the precision."
      //
      // On BSD, it's
      // "The argument is printed in style f (F) or in style e (E)
      // whichever gives full precision in minimum space."

      mp_integer _exponent, _fraction;
      extract_base10(_fraction, _exponent);

      mp_integer adjusted_exponent=base10_digits(_fraction)+_exponent;

      if(adjusted_exponent>=format_spec.precision ||
         adjusted_exponent<-4)
      {
        result+=to_string_scientific(format_spec.precision);
      }
      else
      {
        result+=to_string_decimal(format_spec.precision);

        // Implementations tested also appear to suppress trailing zeros
        // and trailing dots.

        {
          std::size_t trunc_pos=result.find_last_not_of('0');
          if(trunc_pos!=std::string::npos)
            result.resize(trunc_pos+1);
        }

        if(!result.empty() && result.back()=='.')
          result.resize(result.size()-1);
      }
    }
    break;
  }

  while(result.size()<format_spec.min_width)
    result=" "+result;

  return result;
}

mp_integer ieee_floatt::base10_digits(const mp_integer &src)
{
  PRECONDITION(src >= 0);
  mp_integer tmp=src;
  mp_integer result=0;
  while(tmp!=0) { ++result; tmp/=10; }
  return result;
}

std::string ieee_floatt::to_string_decimal(std::size_t precision) const
{
  std::string result;

  if(sign_flag)
    result+='-';

  if((NaN_flag || infinity_flag) && !sign_flag)
    result+='+';

  // special cases
  if(NaN_flag)
    result+="NaN";
  else if(infinity_flag)
    result+="inf";
  else if(is_zero())
  {
    result+='0';

    // add zeros, if needed
    if(precision>0)
    {
      result+='.';
      for(std::size_t i=0; i<precision; i++)
        result+='0';
    }
  }
  else
  {
    mp_integer _exponent, _fraction;
    extract_base2(_fraction, _exponent);

    // convert to base 10
    if(_exponent>=0)
    {
      result+=integer2string(_fraction*power(2, _exponent));

      // add dot and zeros, if needed
      if(precision>0)
      {
        result+='.';
        for(std::size_t i=0; i<precision; i++)
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
      if(position>precision)
      {
        mp_integer r=power(10, position-precision);
        mp_integer remainder=_fraction%r;
        _fraction/=r;
        // not sure if this is the right kind of rounding here
        if(remainder>=r/2)
          ++_fraction;
        position=precision;
      }

      std::string tmp=integer2string(_fraction);

      // pad with zeros from the front, if needed
      while(mp_integer(tmp.size())<=position) tmp="0"+tmp;

      std::size_t dot=tmp.size()-integer2size_t(position);
      result+=std::string(tmp, 0, dot)+'.';
      result+=std::string(tmp, dot, std::string::npos);

      // append zeros if needed
      for(mp_integer i=position; i<precision; ++i)
        result+='0';
      #else

      result+=integer2string(_fraction);

      if(_exponent!=0)
        result+="*2^"+integer2string(_exponent);

      #endif
    }
  }

  return result;
}

/// format as [-]d.ddde+-d Note that printf always produces at least two digits
/// for the exponent.
std::string ieee_floatt::to_string_scientific(std::size_t precision) const
{
  std::string result;

  if(sign_flag)
    result+='-';

  if((NaN_flag || infinity_flag) && !sign_flag)
    result+='+';

  // special cases
  if(NaN_flag)
    result+="NaN";
  else if(infinity_flag)
    result+="inf";
  else if(is_zero())
  {
    result+='0';

    // add zeros, if needed
    if(precision>0)
    {
      result+='.';
      for(std::size_t i=0; i<precision; i++)
        result+='0';
    }

    result+="e0";
  }
  else
  {
    mp_integer _exponent, _fraction;
    extract_base10(_fraction, _exponent);

    // C99 appears to say that conversion to decimal should
    // use the currently selected IEEE rounding mode.
    if(base10_digits(_fraction)>precision+1)
    {
      // re-align
      mp_integer distance=base10_digits(_fraction)-(precision+1);
      mp_integer p=power(10, distance);
      mp_integer remainder=_fraction%p;
      _fraction/=p;
      _exponent+=distance;

      if(remainder==p/2)
      {
        // need to do rounding mode here
        ++_fraction;
      }
      else if(remainder>p/2)
        ++_fraction;
    }

    std::string decimals=integer2string(_fraction);

    CHECK_RETURN(!decimals.empty());

    // First add top digit to result.
    result+=decimals[0];

    // Now add dot and further zeros, if needed.
    if(precision>0)
    {
      result+='.';

      while(decimals.size()<precision+1)
        decimals+='0';

      result+=decimals.substr(1, precision);
    }

    // add exponent
    result+='e';

    std::string exponent_str=
      integer2string(base10_digits(_fraction)+_exponent-1);

    if(!exponent_str.empty() && exponent_str[0]!='-')
      result+='+';

    result+=exponent_str;
  }

  return result;
}

void ieee_floatt::unpack(const mp_integer &i)
{
  PRECONDITION(spec.f != 0);
  PRECONDITION(spec.e != 0);

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

bool ieee_floatt::is_normal() const
{
  return fraction>=power(2, spec.f);
}

mp_integer ieee_floatt::pack() const
{
  mp_integer result=0;

  // sign bit
  if(sign_flag)
    result+=power(2, spec.e+spec.f);

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
    // zero
  }
  else if(is_normal()) // normal?
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

void ieee_floatt::extract_base2(
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

void ieee_floatt::extract_base10(
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

  // now make it base 10
  if(_exponent>=0)
  {
    _fraction*=power(2, _exponent);
    _exponent=0;
  }
  else // _exponent<0
  {
    // 10/2=5 -- this makes it base 10
    _fraction*=power(5, -_exponent);
  }

  // try to re-normalize
  while((_fraction%10)==0)
  {
    _fraction/=10;
    ++_exponent;
  }
}

void ieee_floatt::build(
  const mp_integer &_fraction,
  const mp_integer &_exponent)
{
  sign_flag=_fraction<0;
  fraction=_fraction;
  if(sign_flag)
    fraction=-fraction;
  exponent=_exponent;
  exponent+=spec.f;
  align();
}

/// compute f * (10^e)
void ieee_floatt::from_base10(
  const mp_integer &_fraction,
  const mp_integer &_exponent)
{
  NaN_flag=infinity_flag=false;
  sign_flag=_fraction<0;
  fraction=_fraction;
  if(sign_flag)
    fraction=-fraction;
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

void ieee_floatt::from_integer(const mp_integer &i)
{
  NaN_flag=infinity_flag=sign_flag=false;
  exponent=spec.f;
  fraction=i;
  align();
}

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

  std::size_t lowPower2=fraction.floorPow2();
  mp_integer exponent_offset=0;

  if(lowPower2<spec.f) // too small
  {
    exponent_offset-=(spec.f-lowPower2);

    INVARIANT(
      fraction * power(2, (spec.f - lowPower2)) >= f_power,
      "normalisation result must be >= lower bound");
    INVARIANT(
      fraction * power(2, (spec.f - lowPower2)) < f_power_next,
      "normalisation result must be < upper bound");
  }
  else if(lowPower2>spec.f)  // too large
  {
    exponent_offset+=(lowPower2-spec.f);

    INVARIANT(
      fraction / power(2, (lowPower2 - spec.f)) >= f_power,
      "normalisation result must be >= lower bound");
    INVARIANT(
      fraction / power(2, (lowPower2 - spec.f)) < f_power_next,
      "normalisation result must be < upper bound");
  }

  mp_integer biased_exponent=exponent+exponent_offset+spec.bias();

  // exponent too large (infinity)?
  if(biased_exponent>=spec.max_exponent())
  {
    // we need to consider the rounding mode here
    switch(rounding_mode)
    {
    case UNKNOWN:
    case NONDETERMINISTIC:
    case ROUND_TO_EVEN:
      infinity_flag=true;
      break;

    case ROUND_TO_MINUS_INF:
      // the result of the rounding is never larger than the argument
      if(sign_flag)
        infinity_flag=true;
      else
        make_fltmax();
      break;

    case ROUND_TO_PLUS_INF:
      // the result of the rounding is never smaller than the argument
      if(sign_flag)
      {
        make_fltmax();
        sign_flag=true; // restore sign
      }
      else
        infinity_flag=true;
      break;

    case ROUND_TO_ZERO:
      if(sign_flag)
      {
        make_fltmax();
        sign_flag=true; // restore sign
      }
      else
        make_fltmax(); // positive
      break;
    }

    return; // done
  }
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
      UNREACHABLE;
    }
  }
}

constant_exprt ieee_floatt::to_expr() const
{
  return constant_exprt(integer2bv(pack(), spec.width()), spec.to_type());
}

ieee_floatt &ieee_floatt::operator/=(const ieee_floatt &other)
{
  PRECONDITION(other.spec.f == spec.f);

  // NaN/x = NaN
  if(NaN_flag)
    return *this;

  // x/NaN = NaN
  if(other.NaN_flag)
  {
    make_NaN();
    return *this;
  }

  // 0/0 = NaN
  if(is_zero() && other.is_zero())
  {
    make_NaN();
    return *this;
  }

  // x/0 = +-inf
  if(other.is_zero())
  {
    infinity_flag=true;
    if(other.sign_flag)
      negate();
    return *this;
  }

  // x/inf = NaN
  if(other.infinity_flag)
  {
    if(infinity_flag)
    {
      make_NaN();
      return *this;
    }

    bool old_sign=sign_flag;
    make_zero();
    sign_flag=old_sign;

    if(other.sign_flag)
      negate();

    return *this;
  } // inf/x = inf
  else if(infinity_flag)
  {
    if(other.sign_flag)
      negate();

    return *this;
  }

  exponent-=other.exponent;
  fraction*=power(2, spec.f);

  // to account for error
  fraction*=power(2, spec.f);
  exponent-=spec.f;

  fraction/=other.fraction;

  if(other.sign_flag)
    negate();

  align();

  return *this;
}

ieee_floatt &ieee_floatt::operator*=(const ieee_floatt &other)
{
  PRECONDITION(other.spec.f == spec.f);

  if(other.NaN_flag)
    make_NaN();
  if(NaN_flag)
    return *this;

  if(infinity_flag || other.infinity_flag)
  {
    if(is_zero() || other.is_zero())
    {
      // special case Inf * 0 is NaN
      make_NaN();
      return *this;
    }

    if(other.sign_flag)
      negate();
    infinity_flag=true;
    return *this;
  }

  exponent+=other.exponent;
  exponent-=spec.f;
  fraction*=other.fraction;

  if(other.sign_flag)
    negate();

  align();

  return *this;
}

ieee_floatt &ieee_floatt::operator+=(const ieee_floatt &other)
{
  PRECONDITION(other.spec == spec);
  ieee_floatt _other=other;

  if(other.NaN_flag)
    make_NaN();
  if(NaN_flag)
    return *this;

  if(infinity_flag && other.infinity_flag)
  {
    if(sign_flag==other.sign_flag)
      return *this;
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

  // 0 + 0 needs special treatment for the signs
  if(is_zero() && other.is_zero())
  {
    if(get_sign()==other.get_sign())
      return *this;
    else
    {
      if(rounding_mode==ROUND_TO_MINUS_INF)
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

  INVARIANT(
    exponent == _other.exponent,
    "prior block equalises the exponents by setting both to the "
    "minimum of their previous values while adjusting the mantissa");

  if(sign_flag)
    fraction.negate();
  if(_other.sign_flag)
    _other.fraction.negate();

  fraction+=_other.fraction;

  // if the result is zero,
  // there is some set of rules to get the sign
  if(fraction==0)
  {
    if(rounding_mode==ROUND_TO_MINUS_INF)
      sign_flag=true;
    else
      sign_flag=false;
  }
  else // fraction!=0
  {
    sign_flag=(fraction<0);
    if(sign_flag)
      fraction.negate();
  }

  align();

  return *this;
}

ieee_floatt &ieee_floatt::operator-=(const ieee_floatt &other)
{
  ieee_floatt _other=other;
  _other.sign_flag=!_other.sign_flag;
  return (*this)+=_other;
}

bool ieee_floatt::operator<(const ieee_floatt &other) const
{
  if(NaN_flag || other.NaN_flag)
    return false;

  // check both zero?
  if(is_zero() && other.is_zero())
    return false;

  // one of them zero?
  if(is_zero())
    return !other.sign_flag;
  else if(other.is_zero())
    return sign_flag;

  // check sign
  if(sign_flag!=other.sign_flag)
    return sign_flag;

  // handle infinity
  if(infinity_flag)
  {
    if(other.infinity_flag)
      return false;
    else
      return sign_flag;
  }
  else if(other.infinity_flag)
    return !sign_flag;

  // check exponent
  if(exponent!=other.exponent)
  {
    if(sign_flag) // both negative
      return exponent>other.exponent;
    else
      return exponent<other.exponent;
  }

  // check significand
  if(sign_flag) // both negative
    return fraction>other.fraction;
  else
    return fraction<other.fraction;
}

bool ieee_floatt::operator<=(const ieee_floatt &other) const
{
  if(NaN_flag || other.NaN_flag)
    return false;

  // check zero
  if(is_zero() && other.is_zero())
    return true;

  // handle infinity
  if(infinity_flag && other.infinity_flag &&
     sign_flag==other.sign_flag)
    return true;

  if(!infinity_flag && !other.infinity_flag &&
     sign_flag==other.sign_flag &&
     exponent==other.exponent &&
     fraction==other.fraction)
    return true;

  return *this<other;
}

bool ieee_floatt::operator>(const ieee_floatt &other) const
{
  return other<*this;
}

bool ieee_floatt::operator>=(const ieee_floatt &other) const
{
  return other<=*this;
}

bool ieee_floatt::operator==(const ieee_floatt &other) const
{
  // packed equality!
  if(NaN_flag && other.NaN_flag)
    return true;
  else if(NaN_flag || other.NaN_flag)
    return false;

  if(infinity_flag && other.infinity_flag &&
     sign_flag==other.sign_flag)
    return true;
  else if(infinity_flag || other.infinity_flag)
    return false;

  // if(a.is_zero() && b.is_zero()) return true;

  return
    exponent==other.exponent &&
    fraction==other.fraction &&
    sign_flag==other.sign_flag;
}

bool ieee_floatt::ieee_equal(const ieee_floatt &other) const
{
  if(NaN_flag || other.NaN_flag)
    return false;
  if(is_zero() && other.is_zero())
    return true;
  PRECONDITION(spec == other.spec);
  return *this==other;
}

bool ieee_floatt::operator==(int i) const
{
  ieee_floatt other(spec);
  other.from_integer(i);
  return *this==other;
}

bool ieee_floatt::operator!=(const ieee_floatt &other) const
{
  return !(*this==other);
}

bool ieee_floatt::ieee_not_equal(const ieee_floatt &other) const
{
  if(NaN_flag || other.NaN_flag)
    return true; // !!!
  if(is_zero() && other.is_zero())
    return false;
  PRECONDITION(spec == other.spec);
  return *this!=other;
}

void ieee_floatt::change_spec(const ieee_float_spect &dest_spec)
{
  mp_integer _exponent=exponent-spec.f;
  mp_integer _fraction=fraction;

  if(sign_flag)
    _fraction.negate();

  spec=dest_spec;

  if(_fraction==0)
  {
    // We have a zero. It stays a zero.
    // Don't call build to preserve sign.
  }
  else
    build(_fraction, _exponent);
}

void ieee_floatt::from_expr(const constant_exprt &expr)
{
  spec=ieee_float_spect(to_floatbv_type(expr.type()));
  unpack(bv2integer(id2string(expr.get_value()), false));
}

mp_integer ieee_floatt::to_integer() const
{
  if(NaN_flag || infinity_flag || is_zero())
    return 0;

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

void ieee_floatt::from_double(const double d)
{
  spec.f=52;
  spec.e=11;
  DATA_INVARIANT(spec.width() == 64, "width must be 64 bits");

  static_assert(
    std::numeric_limits<double>::is_iec559,
    "this requires the double layout is according to the ieee754 "
    "standard");
  static_assert(
    sizeof(double) == sizeof(std::uint64_t), "ensure double has 64 bit width");

  union
  {
    double d;
    std::uint64_t i;
  } u;

  u.d=d;

  unpack(u.i);
}

void ieee_floatt::from_float(const float f)
{
  spec.f=23;
  spec.e=8;
  DATA_INVARIANT(spec.width() == 32, "width must be 32 bits");

  static_assert(
    std::numeric_limits<float>::is_iec559,
    "this requires the float layout is according to the ieee754 "
    "standard");
  static_assert(
    sizeof(float) == sizeof(std::uint32_t), "ensure float has 32 bit width");

  union
  {
    float f;
    std::uint32_t i;
  } u;

  u.f=f;

  unpack(u.i);
}

void ieee_floatt::make_NaN()
{
  NaN_flag=true;
  // sign=false;
  exponent=0;
  fraction=0;
  infinity_flag=false;
}

void ieee_floatt::make_fltmax()
{
  mp_integer bit_pattern=
    power(2, spec.e+spec.f)-1-power(2, spec.f);
  unpack(bit_pattern);
}

void ieee_floatt::make_fltmin()
{
  unpack(power(2, spec.f));
}

void ieee_floatt::make_plus_infinity()
{
  NaN_flag=false;
  sign_flag=false;
  exponent=0;
  fraction=0;
  infinity_flag=true;
}

void ieee_floatt::make_minus_infinity()
{
  make_plus_infinity();
  sign_flag=true;
}

bool ieee_floatt::is_double() const
{
  return spec.f==52 && spec.e==11;
}

bool ieee_floatt::is_float() const
{
  return spec.f==23 && spec.e==8;
}

/// Note that calling from_double -> to_double can return different bit patterns
/// for NaN.
double ieee_floatt::to_double() const
{
  PRECONDITION(spec == ieee_float_spect::double_precision());
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

  mp_integer i=pack();
  CHECK_RETURN(i.is_ulong());
  CHECK_RETURN(i <= std::numeric_limits<std::uint64_t>::max());

  a.i=i.to_ulong();
  return a.f;
}

/// Note that calling from_float -> to_float can return different bit patterns
/// for NaN.
float ieee_floatt::to_float() const
{
  // if false - ieee_floatt::to_float not supported on this architecture
  static_assert(
    std::numeric_limits<float>::is_iec559,
    "this requires the float layout is according to the IEC 559/IEEE 754 "
    "standard");
  static_assert(
    sizeof(float) == sizeof(uint32_t), "a 32 bit float type is required");

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

  mp_integer i=pack();
  CHECK_RETURN(i.is_ulong());
  CHECK_RETURN(i <= std::numeric_limits<std::uint32_t>::max());

  a.i=i.to_ulong();
  return a.f;
}

/// Sets *this to the next representable number closer to plus infinity (greater
/// = true) or minus infinity (greater = false).
void ieee_floatt::next_representable(bool greater)
{
  if(is_NaN())
    return;

  bool old_sign=get_sign();

  if(is_zero())
  {
    unpack(1);
    set_sign(!greater);

    return;
  }

  if(is_infinity())
  {
    if(get_sign()==greater)
    {
      make_fltmax();
      set_sign(old_sign);
    }
    return;
  }

  bool dir;
  if(greater)
    dir=!get_sign();
  else
    dir=get_sign();

  set_sign(false);

  mp_integer old=pack();
  if(dir)
    ++old;
  else
    --old;

  unpack(old);

  // sign change impossible (zero case caught earlier)
  set_sign(old_sign);
}
