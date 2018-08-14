/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// expr2cleanct

#include "expr2cleanc.h"
#include <ansi-c/c_qualifiers.h>

/// To convert a type in to ANSI-C but with the identifier in place.
/// This is useful for array types where the identifier is inside the type
/// \param src: the type to convert6
/// \param identifier: the identifier to use as the type
/// \return A C declaration of the given type with the right identifier.
std::string expr2cleanct::convert_with_identifier(
  const typet &src,
  const std::string &identifier)
{
  return convert_rec(src, c_qualifierst(), identifier);
}

/// To produce C code for assigning a struct. The clean version removes padding
/// variables.
/// \param src: The struct expression being converted
/// \param precedence
/// \return C assignment of a struct
std::string expr2cleanct::convert_struct(const exprt &src, unsigned &precedence)
{
  // Generate the normal struct code except we exclude padding members
  return expr2ct::convert_struct(src, precedence, false);
}

/// To produce a C type declaration for a given struct.
/// The clean version removes padding and redefining the struct in line.
/// \param src: The struct type being converted
/// \param qualifer_str: Type qualifiers
/// \param declarator_str: Type declarators
/// \return C type declaration for struct
std::string expr2cleanct::convert_struct_type(
  const typet &src,
  const std::string &qualifer_str,
  const std::string &declarator_str)
{
  // Disable including the body of the struct when getting the type
  return expr2ct::convert_struct_type(
    src, qualifer_str, declarator_str, false, false);
}

/// To produce a C type declaration for a given array.
/// The clean version removes specifying the size of the array
/// \param src: The array type being converted
/// \param qualifiers: Type qualifiers
/// \param declarator_str: Type declarators
/// \return C type declaration for an array
std::string expr2cleanct::convert_array_type(
  const typet &src,
  const qualifierst &qualifiers,
  const std::string &declarator_str)
{
  return expr2ct::convert_array_type(src, qualifiers, declarator_str, false);
}

/// Output C code for a boolean literal. Clean version uses 1 and 0, otherwise
/// requires additional includes.
/// \param boolean_value: The boolean value to convert
/// \return C code for representing a true or false value
std::string expr2cleanct::convert_constant_bool(bool boolean_value)
{
  // This requires #include <stdbool.h>
  return boolean_value?"1":"0";
}
