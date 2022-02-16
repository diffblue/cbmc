/*******************************************************************\

Module: API to expression classes

Author: Malte Mues <mail.mues@gmail.com>

\*******************************************************************/

#ifndef CPROVER_UTIL_C_TYPES_UTIL_H
#define CPROVER_UTIL_C_TYPES_UTIL_H

/// \file
/// This file contains functions, that should support test for underlying
/// c types, in cases where this is required for analysis purpose.

#include "arith_tools.h"
#include "invariant.h"
#include "std_types.h"
#include "type.h"

#include <algorithm>
#include <string>

/// This function checks, whether this has been a char type in the c program.
inline bool is_c_char_type(const typet &type)
{
  const irep_idt &c_type = type.get(ID_C_c_type);
  return is_signed_or_unsigned_bitvector(type) &&
         (c_type == ID_char || c_type == ID_unsigned_char ||
          c_type == ID_signed_char);
}

/// This function checks, whether the type
/// has been a bool type in the c program.
inline bool is_c_bool_type(const typet &type)
{
  return type.id() == ID_c_bool;
}

/// This function checks, whether the type has been some kind of integer
/// type in the c program.
/// It considers the signed and unsigned verison of
/// int, short, long and long long as integer types in c.
inline bool is_c_integral_type(const typet &type)
{
  const irep_idt &c_type = type.get(ID_C_c_type);
  return is_signed_or_unsigned_bitvector(type) &&
         (c_type == ID_signed_int || c_type == ID_unsigned_int ||
          c_type == ID_signed_short_int || c_type == ID_unsigned_int ||
          c_type == ID_unsigned_short_int || c_type == ID_signed_long_int ||
          c_type == ID_signed_long_long_int || c_type == ID_unsigned_long_int ||
          c_type == ID_unsigned_long_long_int);
}

/// This function checks, whether type is a pointer and the target type
/// of the pointer has been a char type in the c program.
inline bool is_c_char_pointer_type(const typet &type)
{
  return type.id() == ID_pointer &&
         is_c_char_type(to_pointer_type(type).base_type());
}

/// This function checks, whether type is a pointer and the target type
/// has been some kind of int type in the c program.
/// is_c_int_derivate answers is used for checking the int type.
inline bool is_c_integral_pointer_type(const typet &type)
{
  return type.id() == ID_pointer &&
         is_c_integral_type(to_pointer_type(type).base_type());
}

/// This function checks, whether the type
/// has been an enum type in the c program.
inline bool is_c_enum_type(const typet &type)
{
  return type.id() == ID_c_enum;
}

/// This function creates a constant representing the
/// bitvector encoded integer value of a string in the enum.
/// \param member_name is a string that should be in the enum.
/// \param c_enum the enum type \p member_name is supposed to be part of.
/// \return constant, that could be assigned as the value of an expression with
///   type c_enum.
inline constant_exprt convert_member_name_to_enum_value(
  const irep_idt &member_name,
  const c_enum_typet &c_enum)
{
  for(const auto &enum_value : c_enum.members())
  {
    if(enum_value.get_identifier() == member_name)
    {
      auto maybe_int_value = numeric_cast<mp_integer>(
        constant_exprt{enum_value.get_value(), typet{ID_bv}});
      CHECK_RETURN(maybe_int_value.has_value());
      return from_integer(*maybe_int_value, c_enum);
    }
  }
  INVARIANT(false, "member_name must be a valid value in the c_enum.");
}

/// Convert id to a Boolean value
/// \param bool_value: A string that is compared to "true" ignoring case.
/// \return a constant of type Boolean
inline bool id2boolean(const std::string &bool_value)
{
  std::string string_value = bool_value;
  std::transform(
    string_value.begin(), string_value.end(), string_value.begin(), ::tolower);
  if(string_value == "true")
    return true;
  if(string_value == "false")
    return false;
  UNREACHABLE;
}

/// This function creates a constant representing either 0 or 1 as value of
/// type type.
/// \param bool_value: A Boolean value.
/// \param type: The type, the resulting constant is supposed to have.
/// \return a constant of type \p type with either 0 or 1 as value.
inline constant_exprt from_c_boolean_value(bool bool_value, const typet &type)
{
  return bool_value ? from_integer(mp_integer(1), type)
                    : from_integer(mp_integer(0), type);
}
#endif // CPROVER_UTIL_C_TYPES_UTIL_H
