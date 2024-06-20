/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_MP_ARITH_H
#define CPROVER_UTIL_MP_ARITH_H

#include "invariant.h"

#include <iosfwd>
#include <string>

#include "big-int/bigint.hh"

// NOLINTNEXTLINE(readability/identifiers)
typedef BigInt mp_integer;

std::ostream &operator<<(std::ostream &, const mp_integer &);
mp_integer operator>>(const mp_integer &, const mp_integer &);
mp_integer operator<<(const mp_integer &, const mp_integer &);
mp_integer bitwise_or(const mp_integer &, const mp_integer &);
mp_integer bitwise_and(const mp_integer &, const mp_integer &);
mp_integer bitwise_xor(const mp_integer &, const mp_integer &);

mp_integer arith_left_shift(
  const mp_integer &, const mp_integer &, std::size_t true_size);

mp_integer arith_right_shift(
  const mp_integer &, const mp_integer &, std::size_t true_size);

mp_integer logic_left_shift(
  const mp_integer &, const mp_integer &, std::size_t true_size);

mp_integer logic_right_shift(
  const mp_integer &, const mp_integer &, std::size_t true_size);

mp_integer rotate_right(
  const mp_integer &, const mp_integer &, std::size_t true_size);

mp_integer rotate_left(
  const mp_integer &, const mp_integer &, std::size_t true_size);

const std::string integer2string(const mp_integer &, unsigned base=10);
const mp_integer string2integer(const std::string &, unsigned base=10);
const std::string integer2binary(const mp_integer &, std::size_t width);
const mp_integer binary2integer(const std::string &, bool is_signed);

// https://www.fluentcpp.com/2016/12/08/strong-types-for-strong-interfaces/
#define BITS_COMPARISON(op)                                                    \
  bool operator op(const bitst &other) const                                   \
  {                                                                            \
    return static_cast<const mp_integer &>(*this)                              \
      op static_cast<const mp_integer &>(other);                               \
  }                                                                            \
  bool operator op(const mp_integer &other) const = delete

template <typename Tag>
class named_mp_integert
{
public:
  explicit named_mp_integert(const mp_integer &generic) : value(generic)
  {
  }

  explicit named_mp_integert(mp_integer &&generic) : value(std::move(generic))
  {
  }

  const mp_integer &get() const
  {
    return value;
  }

  named_mp_integert &operator+=(const named_mp_integert &other)
  {
    value += other.value;
    return *this;
  }

  named_mp_integert &operator-=(const named_mp_integert &other)
  {
    value -= other.value;
    return *this;
  }

  named_mp_integert &operator%=(const named_mp_integert &other)
  {
    value %= other.value;
    return *this;
  }

  bool operator<(const named_mp_integert &other) const
  {
    return value < other.value;
  }

  bool operator>(const named_mp_integert &other) const
  {
    return value > other.value;
  }

  bool operator<=(const named_mp_integert &other) const
  {
    return value <= other.value;
  }

  bool operator>=(const named_mp_integert &other) const
  {
    return value >= other.value;
  }

  bool operator==(const named_mp_integert &other) const
  {
    return value == other.value;
  }

  bool operator!=(const named_mp_integert &other) const
  {
    return value != other.value;
  }

private:
  mp_integer value;
};

template <typename T>
inline named_mp_integert<T>
operator+(const named_mp_integert<T> &lhs, const named_mp_integert<T> &rhs)
{
  return named_mp_integert<T>{lhs} += rhs;
}

template <typename T>
inline named_mp_integert<T>
operator-(const named_mp_integert<T> &lhs, const named_mp_integert<T> &rhs)
{
  return named_mp_integert<T>{lhs} -= rhs;
}

template <typename T>
inline named_mp_integert<T>
operator*(const named_mp_integert<T> &lhs, const mp_integer &rhs)
{
  return named_mp_integert<T>{lhs.get() * rhs};
}

template <typename T>
inline named_mp_integert<T>
operator*(const mp_integer &lhs, const named_mp_integert<T> &rhs)
{
  return named_mp_integert<T>{lhs * rhs.get()};
}

template <typename T>
inline named_mp_integert<T>
operator%(const named_mp_integert<T> &lhs, const named_mp_integert<T> &rhs)
{
  PRECONDITION(rhs.get() > 0);
  return named_mp_integert<T>{lhs} %= rhs;
}

template <typename T>
inline mp_integer
operator/(const named_mp_integert<T> &lhs, const named_mp_integert<T> &rhs)
{
  // division yields just a number
  PRECONDITION(rhs.get() > 0);
  return lhs.get() / rhs.get();
}

template <typename T>
inline std::ostream &
operator<<(std::ostream &os, const named_mp_integert<T> &value)
{
  os << value.get();
  return os;
}

struct bits_tagt
{
};
using bitst = named_mp_integert<bits_tagt>;

struct bytes_tagt
{
};
using bytest = named_mp_integert<bytes_tagt>;

/// Convert \p bytes to bits assuming \p bits_per_byte number of bits in one
/// byte.
inline bitst bytes_to_bits(const bytest &bytes, const mp_integer &bits_per_byte)
{
  return bitst{bytes.get() * bits_per_byte};
}

/// Convert \p bits to bytes assuming \p bits_per_byte number of bits in one
/// byte, rounding downwards.
inline bytest
bits_to_bytes_trunc(const bitst &bits, const mp_integer &bits_per_byte)
{
  PRECONDITION(bits_per_byte > 0);
  return bytest{bits.get() / bits_per_byte};
}

/// Convert \p bits to bytes assuming \p bits_per_byte number of bits in one
/// byte, rounding upwards.
inline bytest
bits_to_bytes_ceil(const bitst &bits, const mp_integer &bits_per_byte)
{
  PRECONDITION(bits_per_byte > 0);
  return bytest{(bits.get() + bits_per_byte - 1) / bits_per_byte};
}

#endif // CPROVER_UTIL_MP_ARITH_H
