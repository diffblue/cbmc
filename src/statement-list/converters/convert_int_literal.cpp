/*******************************************************************\

Module: Statement List Language Conversion

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Conversion

#include "convert_int_literal.h"
#include "convert_dint_literal.h"
#include "statement_list_types.h"

#include <algorithm>
#include <stdexcept>
#include <util/arith_tools.h>
#include <util/std_types.h>

/// Maximum value of integer literals.
#define STL_INT_MAX_VALUE 32767LL
/// Minimum value of integer literals.
#define STL_INT_MIN_VALUE -32768LL
/// Base of decimal integer literals.
#define BASE_10 10u
/// Base of hexadecimal integer literals.
#define BASE_16 16u
/// Base of binary integer literals.
#define BASE_2 2u
/// Character between a prefix and another prefix or the actual literal.
#define PREFIX_SEPARATOR '#'
/// Message for the case of a literal being out of range.
#define OUT_OF_RANGE_MSG "Int literal out of range"

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

constant_exprt convert_int_dec_literal(const std::string &src)
{
  long long literal_value;
  try
  {
    literal_value = get_literal_value(src, BASE_10);
  }
  catch(std::out_of_range &)
  {
    throw std::out_of_range{OUT_OF_RANGE_MSG};
  }
  if(STL_INT_MIN_VALUE <= literal_value && STL_INT_MAX_VALUE >= literal_value)
    return convert_int_dec_literal_value(src);
  else
    return convert_dint_dec_literal_value(src);
}

constant_exprt convert_int_dec_literal_value(const std::string &src)
{
  long long literal_value;
  try
  {
    literal_value = get_literal_value(src, BASE_10);
  }
  catch(std::out_of_range &)
  {
    throw std::out_of_range{OUT_OF_RANGE_MSG};
  }
  if(STL_INT_MIN_VALUE <= literal_value && STL_INT_MAX_VALUE >= literal_value)
    return from_integer(literal_value, get_int_type());
  else
    throw std::out_of_range{OUT_OF_RANGE_MSG};
}

constant_exprt convert_int_hex_literal(const std::string &src)
{
  long long literal_value;
  try
  {
    literal_value = get_literal_value(src, BASE_16);
  }
  catch(std::out_of_range &)
  {
    throw std::out_of_range{OUT_OF_RANGE_MSG};
  }
  if(STL_INT_MIN_VALUE <= literal_value && STL_INT_MAX_VALUE >= literal_value)
    return convert_int_hex_literal_value(src);
  else
    return convert_dint_hex_literal_value(src);
}

constant_exprt convert_int_hex_literal_value(const std::string &src)
{
  long long literal_value;
  try
  {
    literal_value = get_literal_value(src, BASE_16);
  }
  catch(std::out_of_range &)
  {
    throw std::out_of_range{OUT_OF_RANGE_MSG};
  }
  if(STL_INT_MIN_VALUE <= literal_value && STL_INT_MAX_VALUE >= literal_value)
    return from_integer(literal_value, get_int_type());
  else
    throw std::out_of_range{OUT_OF_RANGE_MSG};
}

constant_exprt convert_int_bit_literal(const std::string &src)
{
  long long literal_value;
  try
  {
    literal_value = get_literal_value(src, BASE_2);
  }
  catch(std::out_of_range &)
  {
    throw std::out_of_range{OUT_OF_RANGE_MSG};
  }
  if(STL_INT_MIN_VALUE <= literal_value && STL_INT_MAX_VALUE >= literal_value)
    return convert_int_bit_literal_value(src);
  else
    return convert_dint_bit_literal_value(src);
}

constant_exprt convert_int_bit_literal_value(const std::string &src)
{
  long long literal_value;
  try
  {
    literal_value = get_literal_value(src, BASE_2);
  }
  catch(std::out_of_range &)
  {
    throw std::out_of_range{OUT_OF_RANGE_MSG};
  }
  if(STL_INT_MIN_VALUE <= literal_value && STL_INT_MAX_VALUE >= literal_value)
    return from_integer(literal_value, get_int_type());
  else
    throw std::out_of_range{OUT_OF_RANGE_MSG};
}
