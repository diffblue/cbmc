/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_MP_ARITH_H
#define CPROVER_UTIL_MP_ARITH_H

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

#endif // CPROVER_UTIL_MP_ARITH_H
