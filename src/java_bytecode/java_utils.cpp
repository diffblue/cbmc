/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <string>

#include "java_utils.h"
#include "java_types.h"

constant_exprt as_number(const mp_integer value, const typet &type)
{
  const size_t java_int_width(type.get_unsigned_int(ID_width));
  const std::string significant_bits(integer2string(value, 2));
  std::string binary_width(java_int_width-significant_bits.length(), '0');
  return constant_exprt(binary_width+significant_bits, type);
}
