/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_MP_ARITH_H
#define CPROVER_UTIL_MP_ARITH_H

#include <string>
#include <iosfwd>
#include <limits>

#include "big-int/bigint.hh"
#include "optional.h"

// NOLINTNEXTLINE(readability/identifiers)
typedef BigInt mp_integer;

std::ostream &operator<<(std::ostream &, const mp_integer &);
mp_integer operator>>(const mp_integer &, const mp_integer &);
mp_integer operator<<(const mp_integer &, const mp_integer &);
mp_integer bitwise_or(const mp_integer &, const mp_integer &);
mp_integer bitwise_and(const mp_integer &, const mp_integer &);
mp_integer bitwise_xor(const mp_integer &, const mp_integer &);
mp_integer bitwise_neg(const mp_integer &);

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

/// \deprecated use numeric_cast<unsigned long long> instead
mp_integer::ullong_t integer2ulong(const mp_integer &);

/// \deprecated use numeric_cast<std::size_t> instead
std::size_t integer2size_t(const mp_integer &);

/// \deprecated use numeric_cast<unsigned> instead
unsigned integer2unsigned(const mp_integer &);

const mp_integer mp_zero=string2integer("0");

/// Numerical cast provides a unified way of converting from one numerical type
/// to another.
/// Generic case doesn't exist, this has to be specialized for different types.
template <typename T, typename = void>
struct numeric_castt final
{
};

/// Convert mp_integer to any signed type
/// \tparam T: type to convert to
/// \param mpi: mp_integer to convert
/// \return optional integer of type T if conversion is possible,
///         empty optional otherwise.
template <typename T>
struct numeric_castt<T,
                     typename std::enable_if<std::is_integral<T>::value &&
                                             std::is_signed<T>::value>::type>
{
  static optionalt<T> numeric_cast(const mp_integer &mpi)
  {
    static_assert(
      std::numeric_limits<T>::max() <=
          std::numeric_limits<decltype(mpi.to_long())>::max() &&
        std::numeric_limits<T>::min() >=
          std::numeric_limits<decltype(mpi.to_long())>::min(),
      "Numeric cast only works for types smaller than long long");
    if(
      mpi <= std::numeric_limits<T>::max() &&
      mpi >= std::numeric_limits<T>::min())
      // to_long converts to long long which is the largest signed numeric type
      return {static_cast<T>(mpi.to_long())};
    else
      return {};
  }
};

/// Convert mp_integer to any unsigned type
/// \tparam T: type to convert to
/// \param mpi: mp_integer to convert
/// \return optional integer of type T if conversion is possible,
///         empty optional otherwise.
template <typename T>
struct numeric_castt<T,
                     typename std::enable_if<std::is_integral<T>::value &&
                                             !std::is_signed<T>::value>::type>
{
  static optionalt<T> numeric_cast(const mp_integer &mpi)
  {
    static_assert(
      std::numeric_limits<T>::max() <=
          std::numeric_limits<decltype(mpi.to_ulong())>::max() &&
        std::numeric_limits<T>::min() >=
          std::numeric_limits<decltype(mpi.to_ulong())>::min(),
      "Numeric cast only works for types smaller than unsigned long long");
    if(mpi <= std::numeric_limits<T>::max() && mpi >= 0)
      return {static_cast<T>(mpi.to_ulong())};
    else
      return {};
  }
};

template <typename T>
optionalt<T> numeric_cast(const mp_integer &mpi)
{
  return numeric_castt<T>::numeric_cast(mpi);
}

#endif // CPROVER_UTIL_MP_ARITH_H
