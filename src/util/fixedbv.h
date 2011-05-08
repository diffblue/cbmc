/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FIXEDBV_UTIL_H
#define CPROVER_FIXEDBV_UTIL_H

#include <mp_arith.h>
#include <format_spec.h>

class fixedbv_spect
{
public:
  unsigned integer_bits, width;

  fixedbv_spect():integer_bits(0), width(0)
  {
  }
  
  fixedbv_spect(unsigned _width, unsigned _integer_bits):
    integer_bits(_integer_bits), width(_width)
  {
  }
  
  fixedbv_spect(const class fixedbv_typet &type);

  inline unsigned get_fraction_bits() const
  {
    return width-integer_bits;
  }
};

class fixedbvt
{
public:
  fixedbv_spect spec;
  
  fixedbvt():v(0)
  {
  }

  explicit fixedbvt(const class exprt &expr);

  void from_integer(const mp_integer &i);
  mp_integer to_integer() const; // this rounds to zero
  void from_expr(const class exprt &expr);
  exprt to_expr() const;
  void round(const fixedbv_spect &dest_spec);

  std::string to_ansi_c_string() const
  {
    return format(format_spect());
  }

  std::string format(const format_spect &format_spec) const;

  bool operator == (int i) const;
  bool is_zero() const
  {
    return v==0;
  }
  
  void negate();

  fixedbvt &operator /= (const fixedbvt &other);
  fixedbvt &operator *= (const fixedbvt &other);
  fixedbvt &operator += (const fixedbvt &other);
  fixedbvt &operator -= (const fixedbvt &other);
  
  friend bool operator < (const fixedbvt &a, const fixedbvt &b) { return a.v<b.v; }
  friend bool operator <=(const fixedbvt &a, const fixedbvt &b) { return a.v<=b.v; }
  friend bool operator > (const fixedbvt &a, const fixedbvt &b) { return a.v>b.v; }
  friend bool operator >=(const fixedbvt &a, const fixedbvt &b) { return a.v>=b.v; }
  friend bool operator ==(const fixedbvt &a, const fixedbvt &b) { return a.v==b.v; }
  friend bool operator !=(const fixedbvt &a, const fixedbvt &b) { return a.v!=b.v; }
  
  const mp_integer &get_value() const { return v; }
  void set_value(const mp_integer &_v) { v=_v; }

protected:
  // negative values stored as such
  mp_integer v;
};

bool operator < (const fixedbvt &a, const fixedbvt &b);
bool operator <=(const fixedbvt &a, const fixedbvt &b);
bool operator > (const fixedbvt &a, const fixedbvt &b);
bool operator >=(const fixedbvt &a, const fixedbvt &b);
bool operator ==(const fixedbvt &a, const fixedbvt &b);
bool operator !=(const fixedbvt &a, const fixedbvt &b);

#endif
