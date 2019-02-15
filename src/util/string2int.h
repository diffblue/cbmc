/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/


#ifndef CPROVER_UTIL_STRING2INT_H
#define CPROVER_UTIL_STRING2INT_H

#include "narrow.h"
#include "optional.h"
#include <string>
#include <type_traits>

// These check that the string is indeed a valid number,
// and fail an assertion otherwise.
// We use those for data types that C++11's std::stoi etc. do not
// cover.
unsigned safe_string2unsigned(const std::string &str, int base=10);
std::size_t safe_string2size_t(const std::string &str, int base=10);

// The below mimic C's atoi/atol: any errors are silently ignored.
// They are meant to replace atoi/atol.
int unsafe_string2int(const std::string &str, int base=10);
unsigned unsafe_string2unsigned(const std::string &str, int base=10);
std::size_t unsafe_string2size_t(const std::string &str, int base=10);

// Same for atoll
long long int unsafe_string2signedlonglong(const std::string &str, int base=10);
long long unsigned int unsafe_string2unsignedlonglong(
  const std::string &str, int base=10);

// if we had a `resultt` á la Boost.Outcome (https://ned14.github.io/outcome/)
// we could also return the reason why the conversion failed

/// Convert string to integer as per stoi, but return nullopt when
/// stoi would throw
optionalt<int> string2optional_int(const std::string &, int base = 10);

/// Convert string to unsigned similar to the stoul or stoull functions,
/// return nullopt when the conversion fails.
/// Note: Unlike stoul or stoull negative inputs are disallowed
optionalt<unsigned>
string2optional_unsigned(const std::string &, int base = 10);

/// Convert string to size_t similar to the stoul or stoull functions,
/// return nullopt when the conversion fails.
/// Note: Unlike stoul or stoull negative inputs are disallowed
optionalt<std::size_t>
string2optional_size_t(const std::string &, int base = 10);

/// convert string to signed long long if T is signed
template <typename T>
auto string2optional_base(const std::string &str, int base) ->
  typename std::enable_if<std::is_signed<T>::value, long long>::type
{
  static_assert(
    sizeof(T) <= sizeof(long long),
    "this works under the assumption that long long is the largest type we try "
    "to convert");
  return std::stoll(str, nullptr, base);
}

/// convert string to unsigned long long if T is unsigned
template <typename T>
auto string2optional_base(const std::string &str, int base) ->
  typename std::enable_if<std::is_unsigned<T>::value, unsigned long long>::type
{
  static_assert(
    sizeof(T) <= sizeof(unsigned long long),
    "this works under the assumption that long long is the largest type we try "
    "to convert");
  if(str.find('-') != std::string::npos)
  {
    throw std::out_of_range{
      "unsigned conversion behaves a bit strangely with negative values, "
      "therefore we disable it"};
  }
  return std::stoull(str, nullptr, base);
}

/// attempt a given conversion, return nullopt if the conversion fails
/// with out_of_range or invalid_argument
template <typename do_conversiont>
auto wrap_string_conversion(do_conversiont do_conversion)
  -> optionalt<decltype(do_conversion())>
{
  try
  {
    return do_conversion();
  }
  catch(const std::invalid_argument &)
  {
    return nullopt;
  }
  catch(const std::out_of_range &)
  {
    return nullopt;
  }
}

/// convert a string to an integer, given the base of the representation
/// works with signed and unsigned integer types smaller than
///   (unsigned) long long
/// does not accept negative inputs when the result type is unsigned
template <typename T>
optionalt<T> string2optional(const std::string &str, int base)
{
  return wrap_string_conversion([&]() {
    return narrow_or_throw_out_of_range<T>(string2optional_base<T>(str, base));
  });
}

#endif // CPROVER_UTIL_STRING2INT_H
