/*******************************************************************\

Module: Statement List Language Conversion

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Conversion

#include "convert_dint_literal.h"
#include "statement_list_types.h"

#include <algorithm>
#include <stdexcept>
#include <util/arith_tools.h>
#include <util/std_types.h>

/// Minimum value of double integer literals.
#define STL_DINT_MAX_VALUE 2147483647LL
/// Minimum value of double integer literals.
#define STL_DINT_MIN_VALUE -2147483648LL
/// Base of decimal double integer literals.
#define BASE_10 10u
/// Base of hexadecimal double integer literals.
#define BASE_16 16u
/// Base of binary double integer literals.
#define BASE_2 2u
/// Character between a prefix and another prefix or the actual literal.
#define PREFIX_SEPARATOR '#'
/// Message for the case of a literal being out of range.
#define OUT_OF_RANGE_MSG "DInt literal out of range"

/// Converts the value of a literal the corresponding 'DInt' expression.
/// \param literal_value: Numeric representation of the literal.
/// \return Constant expression representing the double integer value.
static constant_exprt convert_dint_literal_value(const long long literal_value)
{
  if(STL_DINT_MIN_VALUE <= literal_value && STL_DINT_MAX_VALUE >= literal_value)
    return from_integer(literal_value, get_dint_type());
  else
    throw std::out_of_range{OUT_OF_RANGE_MSG};
}

/// Removes every prefix from the given string and converts the remaining
/// string to a number.
/// \param src: String to extract the number from.
/// \param base: Base of the given literal.
/// \return Value of the literal.
static long long get_literal_value(const std::string &src, unsigned int base)
{
  std::string::size_type offset = src.find_last_of(PREFIX_SEPARATOR);
  if(offset == std::string::npos)
    offset = 0u;
  else
    ++offset;
  const std::string literal{src.substr(offset)};
  return std::stoll(literal, nullptr, base);
}

constant_exprt convert_dint_dec_literal_value(const std::string &src)
{
  try
  {
    const long long literal_value = get_literal_value(src, BASE_10);
    return convert_dint_literal_value(literal_value);
  }
  catch(std::out_of_range &)
  {
    throw std::out_of_range{OUT_OF_RANGE_MSG};
  }
}

constant_exprt convert_dint_hex_literal_value(const std::string &src)
{
  try
  {
    const long long literal_value = get_literal_value(src, BASE_16);
    return convert_dint_literal_value(literal_value);
  }
  catch(std::out_of_range &)
  {
    throw std::out_of_range{OUT_OF_RANGE_MSG};
  }
}

constant_exprt convert_dint_bit_literal_value(const std::string &src)
{
  try
  {
    const long long literal_value = get_literal_value(src, BASE_2);
    return convert_dint_literal_value(literal_value);
  }
  catch(std::out_of_range &)
  {
    throw std::out_of_range{OUT_OF_RANGE_MSG};
  }
}
