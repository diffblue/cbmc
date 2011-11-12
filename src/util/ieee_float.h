/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_IEEE_FLOAT_H
#define CPROVER_IEEE_FLOAT_H

#include <iostream>

#include <mp_arith.h>
#include <expr.h>
#include <format_spec.h>

class floatbv_typet;

class ieee_float_spect
{
public:
  unsigned f, e;
  
  mp_integer bias() const;
  
  ieee_float_spect(const floatbv_typet &type)
  {
    from_type(type);
  }
  
  void from_type(const floatbv_typet &type);

  ieee_float_spect():f(0), e(0)
  {
  }

  inline unsigned width() const
  {
    return f+e+1;
  }  

  mp_integer max_exponent() const;
  mp_integer max_fraction() const;
  
  class floatbv_typet to_type() const;
};

class ieee_floatt
{
public:
  // ROUND_TO_EVEN is also known as "round to nearest, ties to even", and
  // is the IEEE default
  typedef enum {
    ROUND_TO_EVEN, ROUND_TO_ZERO, ROUND_TO_PLUS_INF, ROUND_TO_MINUS_INF,
    UNKNOWN, NONDETERMINISTIC }
    rounding_modet;

  rounding_modet rounding_mode;

  ieee_float_spect spec;
  
  ieee_floatt(const ieee_float_spect &_spec):
    rounding_mode(ROUND_TO_EVEN),
    spec(_spec), sign(false), exponent(0), fraction(0),
    NaN(false), infinity(false)
  {
  }
  
  ieee_floatt():
    rounding_mode(ROUND_TO_EVEN),
    sign(false), exponent(0), fraction(0),
    NaN(false), infinity(false)
  {
  }
  
  ieee_floatt(const exprt &expr):
    rounding_mode(ROUND_TO_EVEN)
  {
    from_expr(expr);
  }
  
  void negate()
  {
    sign=!sign;
  }

  void set_sign(bool _sign)
  { sign = _sign; }

  void make_zero()
  {
    sign=false;
    exponent=0;
    fraction=0;
    NaN=false;
    infinity = false;
  }
  
  void make_NaN();
  void make_plus_infinity();
  void make_minus_infinity();
  void make_fltmax();
  void make_fltmin();

  // set to next representable number towards plus or minus infinity
  void increment(bool distinguish_zero=false)
  { 
    if(is_zero() && get_sign() && distinguish_zero)
      negate();
    else
      next_representable(true);
  }

  void decrement(bool distinguish_zero=false)
  { 
    if(is_zero() && !get_sign() && distinguish_zero)
      negate();
    else
      next_representable(false);
  }

  bool is_zero() const {return !NaN && !infinity && fraction==0 && exponent==0;}
  bool get_sign() const { return sign; }
  bool is_NaN() const { return NaN; }
  bool is_infinity() const { return !NaN && infinity; }

  const mp_integer &get_exponent() const { return exponent; }
  const mp_integer &get_fraction() const { return fraction; }
  
  // performs conversion to ieee floating point format
  void from_integer(const mp_integer &i);
  void from_base10(const mp_integer &exp, const mp_integer &frac);
  void build(const mp_integer &exp, const mp_integer &frac);
  void unpack(const mp_integer &i);
  void from_double(const double d);
  void from_float(const float f);

  // perfroms conversions from ieee float-point format
  // to something else
  double to_double() const;
  float to_float() const;
  bool is_double() const;
  bool is_float() const;
  mp_integer pack() const;
  void extract(mp_integer &_exponent, mp_integer &_fraction) const;
  mp_integer to_integer() const; // this rounds to zero

  // conversions
  void change_spec(const ieee_float_spect &dest_spec);

  // output
  void print(std::ostream &out) const;

  std::string to_ansi_c_string() const
  {
    return format(format_spect());
  }
  
  std::string format(const format_spect &format_spec) const;
  
  friend inline std::ostream& operator << (std::ostream &out, const ieee_floatt &f)
  {
    return out << f.to_ansi_c_string();
  }

  // expressions
  exprt to_expr() const;
  void from_expr(const exprt &expr);

  // the usual opertors  
  ieee_floatt &operator /= (const ieee_floatt &other);
  ieee_floatt &operator *= (const ieee_floatt &other);
  ieee_floatt &operator += (const ieee_floatt &other);
  ieee_floatt &operator -= (const ieee_floatt &other);
  
  friend bool operator < (const ieee_floatt &a, const ieee_floatt &b);
  friend bool operator <=(const ieee_floatt &a, const ieee_floatt &b);
  friend bool operator > (const ieee_floatt &a, const ieee_floatt &b);
  friend bool operator >=(const ieee_floatt &a, const ieee_floatt &b);

  // warning: these do packed equality, not IEEE equality
  // e.g., NAN==NAN
  friend bool operator ==(const ieee_floatt &a, const ieee_floatt &b);
  friend bool operator !=(const ieee_floatt &a, const ieee_floatt &b);
  friend bool operator ==(const ieee_floatt &a, int i);

  // these do IEEE equality, i.e., NAN!=NAN
  friend bool ieee_equal(const ieee_floatt &a, const ieee_floatt &b);
  friend bool ieee_not_equal(const ieee_floatt &a, const ieee_floatt &b);
  
protected:
  void divide_and_round(mp_integer &fraction, const mp_integer &factor);
  void align();
  void next_representable(bool greater);

  // we store the number unpacked
  bool sign;
  mp_integer exponent; // this is unbiased
  mp_integer fraction; // this _does_ include the hidden bit
  bool NaN, infinity;
};

bool operator < (const ieee_floatt &a, const ieee_floatt &b);
bool operator <=(const ieee_floatt &a, const ieee_floatt &b);
bool operator > (const ieee_floatt &a, const ieee_floatt &b);
bool operator >=(const ieee_floatt &a, const ieee_floatt &b);
bool operator ==(const ieee_floatt &a, const ieee_floatt &b);
bool operator !=(const ieee_floatt &a, const ieee_floatt &b);
std::ostream& operator << (std::ostream &, const ieee_floatt &);
bool ieee_equal(const ieee_floatt &a, const ieee_floatt &b);
bool ieee_not_equal(const ieee_floatt &a, const ieee_floatt &b);

#endif
