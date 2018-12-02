/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_BV_ARITHMETIC_H
#define CPROVER_UTIL_BV_ARITHMETIC_H

#include <iosfwd>

#include "mp_arith.h"
#include "format_spec.h"

class constant_exprt;
class exprt;
class typet;

class bv_spect
{
public:
  std::size_t width;
  bool is_signed;

  explicit bv_spect(const typet &type)
  {
    from_type(type);
  }

  void from_type(const typet &type);

  bv_spect():width(0), is_signed(false)
  {
  }

  mp_integer max_value() const;
  mp_integer min_value() const;

  typet to_type() const;

  bool operator==(const bv_spect &other) const
  {
    return width==other.width && is_signed==other.is_signed;
  }
};

class bv_arithmetict
{
public:
  bv_spect spec;

  explicit bv_arithmetict(const bv_spect &_spec):
    spec(_spec), value(0)
  {
  }

  bv_arithmetict():value(0)
  {
  }

  explicit bv_arithmetict(const constant_exprt &expr)
  {
    from_expr(expr);
  }

  void negate();

  void make_zero()
  {
    value=0;
  }

  bool is_zero() const { return value==0; }

  // performs conversion to bit-vector format
  void from_integer(const mp_integer &i);

  // performs conversion from ieee floating point format
  void change_spec(const bv_spect &dest_spec);
  mp_integer to_integer() const { return value; }

  void print(std::ostream &out) const;

  std::string to_ansi_c_string() const
  {
    return format(format_spect());
  }

  std::string format(const format_spect &format_spec) const;

  // expressions
  constant_exprt to_expr() const;
  void from_expr(const constant_exprt &expr);

  bv_arithmetict &operator/=(const bv_arithmetict &other);
  bv_arithmetict &operator*=(const bv_arithmetict &other);
  bv_arithmetict &operator+=(const bv_arithmetict &other);
  bv_arithmetict &operator-=(const bv_arithmetict &other);
  bv_arithmetict &operator%=(const bv_arithmetict &other);

  bool operator<(const bv_arithmetict &other);
  bool operator<=(const bv_arithmetict &other);
  bool operator>(const bv_arithmetict &other);
  bool operator>=(const bv_arithmetict &other);
  bool operator==(const bv_arithmetict &other);
  bool operator!=(const bv_arithmetict &other);
  bool operator==(int i);

  std::ostream &operator<<(std::ostream &out)
  {
    return out << to_ansi_c_string();
  }

  // turn into natural number representation
  void unpack(const mp_integer &i) { value=i; adjust(); }
  mp_integer pack() const;

protected:
  // we store negative numbers as such
  mp_integer value;

  // puts the value back into its range
  void adjust();
};

#endif // CPROVER_UTIL_BV_ARITHMETIC_H
