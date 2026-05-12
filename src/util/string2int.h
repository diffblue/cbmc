/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/


#ifndef CPROVER_UTIL_STRING2INT_H
#define CPROVER_UTIL_STRING2INT_H

#include "narrow.h"

#include <charconv>
#include <optional>
#include <string>
#include <string_view>
#include <type_traits>

// These check that the string is indeed a valid number,
// and fail an assertion otherwise.
// We use those for data types that C++11's std::stoi etc. do not
// cover.
unsigned safe_string2unsigned(std::string_view, int base = 10);
std::size_t safe_string2size_t(std::string_view, int base = 10);

// The below mimic C's atoi/atol: any errors are silently ignored.
// They are meant to replace atoi/atol.
int unsafe_string2int(const std::string &, int base = 10);
unsigned unsafe_string2unsigned(const std::string &, int base = 10);
std::size_t unsafe_string2size_t(const std::string &, int base = 10);

// Same for atoll
long long int unsafe_string2signedlonglong(const std::string &, int base = 10);
long long unsigned int
unsafe_string2unsignedlonglong(const std::string &, int base = 10);

// if we had a `resultt` á la Boost.Outcome (https://ned14.github.io/outcome/)
// we could also return the reason why the conversion failed

/// Convert string to integer as per stoi, but return nullopt when
/// stoi would throw
std::optional<int> string2optional_int(std::string_view, int base = 10);

/// Convert string to unsigned similar to the stoul or stoull functions,
/// return nullopt when the conversion fails.
/// Note: Unlike stoul or stoull negative inputs are disallowed
std::optional<unsigned>
string2optional_unsigned(std::string_view, int base = 10);

/// Convert string to size_t similar to the stoul or stoull functions,
/// return nullopt when the conversion fails.
/// Note: Unlike stoul or stoull negative inputs are disallowed
std::optional<std::size_t>
string2optional_size_t(std::string_view, int base = 10);

/// Convert a string to an integer, given the base of the representation,
/// works with signed and unsigned integer types,
/// rejects negative inputs when the result type is unsigned,
/// rejects the empty string,
/// rejects leading spaces,
/// rejects any trailing non-numerical suffix.
/// A prefix such as 0, 0x, 0X to change base is _not_ supported.
template <typename T>
std::optional<T> string2optional(std::string_view str, int base = 10)
{
  PRECONDITION(base == 2 || base == 8 || base == 10 || base == 16);

  static_assert(
    std::is_integral<T>::value, "string2optional requires an integral type");

  if(str.empty())
    return std::nullopt;

  // reject negative inputs for unsigned types
  if(std::is_unsigned<T>::value && str.front() == '-')
    return std::nullopt;

  const char *first = str.data();
  const char *last = str.data() + str.size();

  T value{};
  auto [ptr, ec] = std::from_chars(first, last, value, base);

  if(ec != std::errc{} || ptr != last)
    return std::nullopt;

  return value;
}

#endif // CPROVER_UTIL_STRING2INT_H
