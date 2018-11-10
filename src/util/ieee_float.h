/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_IEEE_FLOAT_H
#define CPROVER_UTIL_IEEE_FLOAT_H

#include <iosfwd>

#include "mp_arith.h"
#include "format_spec.h"
#include "irep.h"
#include "cprover_prefix.h"

class constant_exprt;
class floatbv_typet;

const char ID_cprover_rounding_mode_str[] = CPROVER_PREFIX "rounding_mode";

class ieee_float_spect
{
public:
  // Number of bits for fraction (excluding hidden bit)
  // and exponent, respectively
  std::size_t f, e;

  // x86 has an extended precision format with an explicit
  // integer bit.
  bool x86_extended;

  mp_integer bias() const;

  explicit ieee_float_spect(const floatbv_typet &type)
  {
    from_type(type);
  }

  void from_type(const floatbv_typet &type);

  ieee_float_spect():f(0), e(0), x86_extended(false)
  {
  }

  ieee_float_spect(std::size_t _f, std::size_t _e):
    f(_f), e(_e), x86_extended(false)
  {
  }

  std::size_t width() const
  {
    // Add one for the sign bit.
    // Add one if x86 explicit integer bit is used.
    return f+e+1+(x86_extended?1:0);
  }

  mp_integer max_exponent() const;
  mp_integer max_fraction() const;

  class floatbv_typet to_type() const;

  // this is binary16 in IEEE 754-2008
  static ieee_float_spect half_precision()
  {
    // 16 bits in total
    return ieee_float_spect(10, 5);
  }

  // the well-know standard formats
  static ieee_float_spect single_precision()
  {
    // 32 bits in total
    return ieee_float_spect(23, 8);
  }

  static ieee_float_spect double_precision()
  {
    // 64 bits in total
    return ieee_float_spect(52, 11);
  }

  static ieee_float_spect quadruple_precision()
  {
    // IEEE 754 binary128
    return ieee_float_spect(112, 15);
  }

  static ieee_float_spect x86_80()
  {
    // Intel, not IEEE
    ieee_float_spect result(63, 15);
    result.x86_extended=true;
    return result;
  }

  static ieee_float_spect x86_96()
  {
    // Intel, not IEEE
    ieee_float_spect result(63, 15);
    result.x86_extended=true;
    return result;
  }

  bool operator==(const ieee_float_spect &other) const
  {
    return f==other.f && e==other.e && x86_extended==other.x86_extended;
  }

  bool operator!=(const ieee_float_spect &other) const
  {
    return !(*this==other);
  }
};

class ieee_floatt
{
public:
  // ROUND_TO_EVEN is also known as "round to nearest, ties to even", and
  // is the IEEE default.
  // The numbering below is what x86 uses in the control word.
  enum rounding_modet
  {
    ROUND_TO_EVEN=0, ROUND_TO_MINUS_INF=1,
    ROUND_TO_PLUS_INF=2,  ROUND_TO_ZERO=3,
    UNKNOWN, NONDETERMINISTIC
  };

  rounding_modet rounding_mode;

  ieee_float_spect spec;

  explicit ieee_floatt(const ieee_float_spect &_spec):
    rounding_mode(ROUND_TO_EVEN),
    spec(_spec), sign_flag(false), exponent(0), fraction(0),
    NaN_flag(false), infinity_flag(false)
  {
  }

  explicit ieee_floatt(const floatbv_typet &type):
    rounding_mode(ROUND_TO_EVEN),
    spec(ieee_float_spect(type)),
    sign_flag(false),
    exponent(0),
    fraction(0),
    NaN_flag(false),
    infinity_flag(false)
  {
  }

  ieee_floatt():
    rounding_mode(ROUND_TO_EVEN),
    sign_flag(false), exponent(0), fraction(0),
    NaN_flag(false), infinity_flag(false)
  {
  }

  explicit ieee_floatt(const constant_exprt &expr):
    rounding_mode(ROUND_TO_EVEN)
  {
    from_expr(expr);
  }

  void negate()
  {
    sign_flag=!sign_flag;
  }

  void set_sign(bool _sign)
  { sign_flag = _sign; }

  void make_zero()
  {
    sign_flag=false;
    exponent=0;
    fraction=0;
    NaN_flag=false;
    infinity_flag=false;
  }

  static ieee_floatt zero(const floatbv_typet &type)
  {
    ieee_floatt result(type);
    result.make_zero();
    return result;
  }

  void make_NaN();
  void make_plus_infinity();
  void make_minus_infinity();
  void make_fltmax(); // maximum representable finite floating-point number
  void make_fltmin(); // minimum normalized positive floating-point number

  static ieee_floatt NaN(const ieee_float_spect &_spec)
  { ieee_floatt c(_spec); c.make_NaN(); return c; }

  static ieee_floatt plus_infinity(const ieee_float_spect &_spec)
  { ieee_floatt c(_spec); c.make_plus_infinity(); return c; }

  static ieee_floatt minus_infinity(const ieee_float_spect &_spec)
  { ieee_floatt c(_spec); c.make_minus_infinity(); return c; }

  // maximum representable finite floating-point number
  static ieee_floatt fltmax(const ieee_float_spect &_spec)
  { ieee_floatt c(_spec); c.make_fltmax(); return c; }

  // minimum normalized positive floating-point number
  static ieee_floatt fltmin(const ieee_float_spect &_spec)
  { ieee_floatt c(_spec); c.make_fltmin(); return c; }

  // set to next representable number towards plus infinity
  void increment(bool distinguish_zero=false)
  {
    if(is_zero() && get_sign() && distinguish_zero)
      negate();
    else
      next_representable(true);
  }

  // set to previous representable number towards minus infinity
  void decrement(bool distinguish_zero=false)
  {
    if(is_zero() && !get_sign() && distinguish_zero)
      negate();
    else
      next_representable(false);
  }

  bool is_zero() const
  {
    return !NaN_flag && !infinity_flag && fraction==0 && exponent==0;
  }
  bool get_sign() const { return sign_flag; }
  bool is_NaN() const { return NaN_flag; }
  bool is_infinity() const { return !NaN_flag && infinity_flag; }
  bool is_normal() const;

  const mp_integer &get_exponent() const { return exponent; }
  const mp_integer &get_fraction() const { return fraction; }

  // performs conversion to IEEE floating point format
  void from_integer(const mp_integer &i);
  void from_base10(const mp_integer &exp, const mp_integer &frac);
  void build(const mp_integer &exp, const mp_integer &frac);
  void unpack(const mp_integer &i);
  void from_double(const double d);
  void from_float(const float f);

  // performs conversions from IEEE float-point format
  // to something else
  double to_double() const;
  float to_float() const;
  bool is_double() const;
  bool is_float() const;
  mp_integer pack() const;
  void extract_base2(mp_integer &_exponent, mp_integer &_fraction) const;
  void extract_base10(mp_integer &_exponent, mp_integer &_fraction) const;
  mp_integer to_integer() const; // this always rounds to zero

  // conversions
  void change_spec(const ieee_float_spect &dest_spec);

  // output
  void print(std::ostream &out) const;

  std::string to_ansi_c_string() const
  {
    return format(format_spect());
  }

  std::string to_string_decimal(std::size_t precision) const;
  std::string to_string_scientific(std::size_t precision) const;
  std::string format(const format_spect &format_spec) const;

  // expressions
  constant_exprt to_expr() const;
  void from_expr(const constant_exprt &expr);

  // the usual operators
  ieee_floatt &operator/=(const ieee_floatt &other);
  ieee_floatt &operator*=(const ieee_floatt &other);
  ieee_floatt &operator+=(const ieee_floatt &other);
  ieee_floatt &operator-=(const ieee_floatt &other);

  bool operator<(const ieee_floatt &other) const;
  bool operator<=(const ieee_floatt &other) const;
  bool operator>(const ieee_floatt &other) const;
  bool operator>=(const ieee_floatt &other) const;

  // warning: these do packed equality, not IEEE equality
  // e.g., NAN==NAN
  bool operator==(const ieee_floatt &other) const;
  bool operator!=(const ieee_floatt &other) const;
  bool operator==(int i) const;

  // these do IEEE equality, i.e., NAN!=NAN
  bool ieee_equal(const ieee_floatt &other) const;
  bool ieee_not_equal(const ieee_floatt &other) const;

protected:
  void divide_and_round(mp_integer &dividend, const mp_integer &divisor);
  void align();
  void next_representable(bool greater);

  // we store the number unpacked
  bool sign_flag;
  mp_integer exponent; // this is unbiased
  mp_integer fraction; // this _does_ include the hidden bit
  bool NaN_flag, infinity_flag;

  // number of digits of an integer >=1 in base 10
  static mp_integer base10_digits(const mp_integer &src);
};

inline std::ostream &operator<<(
  std::ostream &out,
  const ieee_floatt &f)
{
  return out << f.to_ansi_c_string();
}

#endif // CPROVER_UTIL_IEEE_FLOAT_H
