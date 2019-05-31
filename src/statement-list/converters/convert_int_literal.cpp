/*******************************************************************\

Module: Statement List Language Conversion

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Conversion

#include "convert_int_literal.h"

#include <algorithm>
#include <util/std_types.h>

/// Hex literals in STL are preceded by '16#'
#define HEX_PREFIX_LENGTH 3
/// Binary literals in STL are preceded by '2#'
#define BINARY_PREFIX_LENGTH 2

constant_exprt convert_int_dec_literal(const std::string &src)
{
  std::string value(src);
  value.erase(std::remove(begin(value), end(value), '+'), end(value));

  signedbv_typet type{16};
  type.set(ID_statement_list_type, ID_statement_list_int);

  return constant_exprt(value, type);
}

constant_exprt convert_int_hex_literal(const std::string &src)
{
  const std::string hex_literal(
    src.substr(HEX_PREFIX_LENGTH, std::string::npos));
  int value = std::stoi(hex_literal, nullptr, 16);

  signedbv_typet type{16};
  type.set(ID_statement_list_type, ID_statement_list_int);

  return constant_exprt(std::to_string(value), type);
}

constant_exprt convert_int_bit_literal(const std::string &src)
{
  const std::string bit_literal(
    src.substr(BINARY_PREFIX_LENGTH, std::string::npos));
  int value = std::stoi(bit_literal, nullptr, 2);

  signedbv_typet type{16};
  type.set(ID_statement_list_type, ID_statement_list_int);

  return constant_exprt{std::to_string(value), type};
}
