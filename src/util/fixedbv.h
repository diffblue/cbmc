/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_FIXEDBV_H
#define CPROVER_UTIL_FIXEDBV_H

#include "mp_arith.h"
#include "format_spec.h"

class constant_exprt;
class fixedbv_typet;

class fixedbv_spect
{
public:
  std::size_t integer_bits, width;

  fixedbv_spect():integer_bits(0), width(0)
  {
  }

  fixedbv_spect(std::size_t _width, std::size_t _integer_bits):
    integer_bits(_integer_bits), width(_width)
  {
  }

  explicit fixedbv_spect(const fixedbv_typet &type);

  std::size_t get_fraction_bits() const
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

  explicit fixedbvt(const fixedbv_spect &_spec):spec(_spec), v(0)
  {
  }

  explicit fixedbvt(const constant_exprt &expr);

  void from_integer(const mp_integer &i);
  mp_integer to_integer() const; // this rounds to zero
  void from_expr(const constant_exprt &expr);
  constant_exprt to_expr() const;
  void round(const fixedbv_spect &dest_spec);

  std::string to_ansi_c_string() const
  {
    return format(format_spect());
  }

  std::string format(const format_spect &format_spec) const;

  bool operator==(int i) const;

  bool is_zero() const
  {
    return v==0;
  }

  static fixedbvt zero(const fixedbv_typet &type)
  {
    return fixedbvt(fixedbv_spect(type));
  }

  void negate();

  fixedbvt &operator/=(const fixedbvt &other);
  fixedbvt &operator*=(const fixedbvt &other);
  fixedbvt &operator+=(const fixedbvt &other);
  fixedbvt &operator-=(const fixedbvt &other);

  bool operator<(const fixedbvt &other) const { return v<other.v; }
  bool operator<=(const fixedbvt &other) const { return v<=other.v; }
  bool operator>(const fixedbvt &other) const { return v>other.v; }
  bool operator>=(const fixedbvt &other) const { return v>=other.v; }
  bool operator==(const fixedbvt &other) const { return v==other.v; }
  bool operator!=(const fixedbvt &other) const { return v!=other.v; }

  const mp_integer &get_value() const { return v; }
  void set_value(const mp_integer &_v) { v=_v; }

protected:
  // negative values stored as such
  mp_integer v;
};

#endif // CPROVER_UTIL_FIXEDBV_H
