// Copyright 2018 Author: Malte Mues <mail.mues@gmail.com>

/// \file
/// This file contains functions, that should support test for underlying
/// c types, in cases where this is required for anlysis purpose.
#ifndef CPROVER_UTIL_C_TYPES_UTIL_H
#define CPROVER_UTIL_C_TYPES_UTIL_H

#include "arith_tools.h"
#include "invariant.h"
#include "std_types.h"
#include "type.h"

#include <algorithm>
#include <string>

/// This function checks, whether this has been a char type in the c program.
inline bool is_c_char(const typet &type)
{
  const irep_idt &c_type = type.get(ID_C_c_type);
  return is_signed_or_unsigned_bitvector(type) &&
         (c_type == ID_char || c_type == ID_unsigned_char ||
          c_type == ID_signed_char);
}

/// This function checks, whether the type
/// has been a bool type in the c program.
inline bool is_c_bool(const typet &type)
{
  return type.id() == ID_c_bool;
}

/// This function checks, whether the type is has been some kind of integer
/// type in the c program.
/// It considers the signed and unsigned verison of
/// int, short, long and long long as integer types in c.
inline bool is_c_int_derivate(const typet &type)
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
inline bool is_c_char_pointer(const typet &type)
{
  return type.id() == ID_pointer && is_c_char(type.subtype());
}

/// This function checks, whether type is a pointer and the target type
/// has been some kind of int type in the c program.
/// is_c_int_derivate answers is used for checking the int type.
inline bool is_c_int_derivate_pointer(const typet &type)
{
  return type.id() == ID_pointer && is_c_int_derivate(type.subtype());
}

/// This function checks, whether the type
/// has been an enum type in the c program.
inline bool is_c_enum(const typet &type)
{
  return type.id() == ID_c_enum;
}

/// This function creates a constant representing the
/// bitvector encoded integer value of a string in the enum.
/// \param member_name is a string that should be in the enum.
/// \param c_enum the enum type memeber_name is supposed to be part of.
/// \return value a constant, that could be assigned as value for an expression
/// with type c_enum.
constant_exprt convert_member_name_to_enum_value(
  const std::string &member_name,
  const c_enum_typet &c_enum)
{
  for(const auto &enum_value : c_enum.members())
  {
    if(id2string(enum_value.get_identifier()) == member_name)
    {
      mp_integer int_value = string2integer(id2string(enum_value.get_value()));
      return from_integer(int_value, c_enum);
    }
  }
  INVARIANT(false, "member_name must be a valid value in the c_enum.");
}

/// This function creates a constant representing either 0 or 1 as value of
/// type type.
/// \param bool_value: A string that is compared to "true" ignoring case.
/// \param type: The type, the resulting constant is supposed to have.
/// \return a constant of type \param type with either 0 or 1 as value.
constant_exprt from_c_boolean_value(std::string bool_value, const typet &type)
{
  std::transform(
    bool_value.begin(), bool_value.end(), bool_value.begin(), ::tolower);
  if(bool_value == "true")
  {
    return from_integer(mp_integer(1), type);
  }
  else
  {
    return from_integer(mp_integer(0), type);
  }
}
#endif // CPROVER_UTIL_C_TYPES_UTIL_H
