#ifndef SYSTEMC_SC_UINT_H
#define SYSTEMC_SC_UINT_H

#include <cassert>
#include "sc_uint_base.h"

template <int W>
class sc_uint : public sc_uint_base
{
 public:
  sc_uint() : sc_uint_base(0, W) {}

  sc_uint(unsigned long v)
    : sc_uint_base(v, W)
  {
  }

  sc_uint(const sc_uint_base &b)
    : sc_uint_base(b.val, W)
  {
  }

  sc_uint(const sc_uint_subref &b)
    : sc_uint_base(b)
  {
  }

  sc_uint<W> &operator=(const sc_uint_base &other)
  {
    sc_uint_base::operator=(other);
    return *this;
  }

  sc_uint<W> &operator=(const sc_uint_subref &other)
  {
    sc_uint_base::operator=(other);
    return *this;
  }

  bool operator==(const sc_uint_base &other)
  {
    return sc_uint_base::operator==(other);
  }

  sc_uint<W> operator += (const sc_uint_base &other)
  {
    return sc_uint_base::operator+=(other);
  }

  sc_uint<W> operator *= (const sc_uint_base &other)
  {
    return sc_uint_base::operator*=(other);
  }

  sc_uint<W> operator+ (const sc_uint_base &other)
  {
    return sc_uint<W>(sc_uint_base::operator+(other));
  }

  sc_uint<W> operator* (const sc_uint_base &other)
  {
    return sc_uint<W>(sc_uint_base::operator*(other));
  }

  sc_uint<W> operator >>= (int v)
  {
    return sc_uint_base::operator>>=(v);
  }

};


#endif
