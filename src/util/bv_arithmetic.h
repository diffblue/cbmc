/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BV_ARITHMETIC_H
#define CPROVER_BV_ARITHMETIC_H

#include <ostream>

#include <mp_arith.h>
#include "format_spec.h"

class exprt;
class typet;

class bv_spect
{
public:
  unsigned width;
  bool is_signed;
  
  bv_spect(const typet &type)
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
};

class bv_arithmetict
{
public:
  bv_spect spec;
  
  bv_arithmetict(const bv_spect &_spec):
    spec(_spec), value(0)
  {
  }
  
  bv_arithmetict():value(0)
  {
  }
  
  bv_arithmetict(const exprt &expr)
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
  exprt to_expr() const;
  void from_expr(const exprt &expr);
  
  bv_arithmetict &operator /= (const bv_arithmetict &other);
  bv_arithmetict &operator *= (const bv_arithmetict &other);
  bv_arithmetict &operator += (const bv_arithmetict &other);
  bv_arithmetict &operator -= (const bv_arithmetict &other);
  bv_arithmetict &operator %= (const bv_arithmetict &other);
  
  friend bool operator < (const bv_arithmetict &a, const bv_arithmetict &b);
  friend bool operator <=(const bv_arithmetict &a, const bv_arithmetict &b);
  friend bool operator > (const bv_arithmetict &a, const bv_arithmetict &b);
  friend bool operator >=(const bv_arithmetict &a, const bv_arithmetict &b);
  friend bool operator ==(const bv_arithmetict &a, const bv_arithmetict &b);
  friend bool operator !=(const bv_arithmetict &a, const bv_arithmetict &b);
  friend bool operator ==(const bv_arithmetict &a, int i);

  friend std::ostream& operator << (std::ostream &out, const bv_arithmetict &f)
  {
    return out << f.to_ansi_c_string();
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

bool operator < (const bv_arithmetict &a, const bv_arithmetict &b);
bool operator <=(const bv_arithmetict &a, const bv_arithmetict &b);
bool operator > (const bv_arithmetict &a, const bv_arithmetict &b);
bool operator >=(const bv_arithmetict &a, const bv_arithmetict &b);
bool operator ==(const bv_arithmetict &a, const bv_arithmetict &b);
bool operator !=(const bv_arithmetict &a, const bv_arithmetict &b);
std::ostream& operator << (std::ostream &, const bv_arithmetict &);

#endif
