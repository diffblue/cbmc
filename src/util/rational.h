/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_RATIONAL_H
#define CPROVER_RATIONAL_H

#include <cassert>
#include <vector>

#include <mp_arith.h>

class exprt;

class rationalt
{
protected:
  mp_integer numerator; // Zaehler
  mp_integer denominator; // Nenner

  void normalize();
  void same_denominator(rationalt &n);

public:
  // constructors
  rationalt():numerator(0), denominator(1) { }
  rationalt(const mp_integer &i):numerator(i), denominator(1) { }
  rationalt(int i):numerator(i), denominator(1) { }

  rationalt &operator+=(const rationalt &n);
  rationalt &operator-=(const rationalt &n);
  rationalt &operator*=(const rationalt &n);
  rationalt &operator/=(const rationalt &n);

  bool operator==(const rationalt &n) const
  {
    rationalt r1(*this), r2(n);
    r1.same_denominator(r2);
    return r1.numerator==r2.numerator;
  }
   
  bool operator!=(const rationalt &n) const
  {
    rationalt r1(*this), r2(n);
    r1.same_denominator(r2);
    return r1.numerator!=r2.numerator;
  }
   
  bool operator<(const rationalt &n) const
  {
    rationalt r1(*this), r2(n);
    r1.same_denominator(r2);
    return r1.numerator<r2.numerator;
  }
   
  bool operator<=(const rationalt &n) const
  {
    rationalt r1(*this), r2(n);
    r1.same_denominator(r2);
    return r1.numerator<=r2.numerator;
  }
   
  bool operator>=(const rationalt &n) const
  {
    return !(*this<n);
  }
   
  bool operator>(const rationalt &n) const
  {
    return !(*this<=n);
  }
   
  bool is_zero() const
  { return numerator.is_zero(); }

  bool is_one() const
  { return !is_zero() && numerator==denominator; }
   
  bool is_negative() const
  { return !is_zero() && numerator.is_negative(); }

  void invert();

  friend rationalt operator+(const rationalt &a, const rationalt &b)
  {
    rationalt tmp(a);
    tmp+=b;
    return tmp;
  }

  friend rationalt operator-(const rationalt &a, const rationalt &b)
  {
    rationalt tmp(a);
    tmp-=b;
    return tmp;
  }

  friend rationalt operator-(const rationalt &a)
  {
    rationalt tmp(a);
    tmp.numerator.negate();
    return tmp;
  }

  friend rationalt operator*(const rationalt &a, const rationalt &b)
  {
    rationalt tmp(a);
    tmp*=b;
    return tmp;
  }

  friend rationalt operator/(const rationalt &a, const rationalt &b)
  {
    rationalt tmp(a);
    tmp/=b;
    return tmp;
  }

  friend std::ostream& operator<< (std::ostream& out, const rationalt &a);
  friend exprt from_rational(const rationalt &n);
};
 
rationalt inverse(const rationalt &n);

#endif
