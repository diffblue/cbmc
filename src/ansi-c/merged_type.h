/*******************************************************************\

Module: A type that holds a combination of types

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_MERGED_TYPE_H
#define CPROVER_ANSI_C_MERGED_TYPE_H

#include <util/type.h>

/// holds a combination of types
class merged_typet : public type_with_subtypest
{
public:
  merged_typet() : type_with_subtypest(ID_merged_type, {})
  {
  }

  typet &last_type()
  {
    return subtypes().back();
  }
};

/// conversion to merged_typet
inline const merged_typet &to_merged_type(const typet &type)
{
  PRECONDITION(type.id() == ID_merged_type);
  DATA_INVARIANT(
    !static_cast<const type_with_subtypest &>(type).subtypes().empty(),
    "merge_typet has at least one subtype");
  return static_cast<const merged_typet &>(type);
}

/// conversion to merged_typet
inline merged_typet &to_merged_type(typet &type)
{
  PRECONDITION(type.id() == ID_merged_type);
  DATA_INVARIANT(
    !static_cast<const type_with_subtypest &>(type).subtypes().empty(),
    "merge_typet has at least one subtype");
  return static_cast<merged_typet &>(type);
}

#endif // CPROVER_ANSI_C_MERGED_TYPE_H
