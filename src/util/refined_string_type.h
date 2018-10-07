/********************************************************************\

Module: Type for string expressions used by the string solver.
        These string expressions contain a field `length`, of type
        `index_type`, a field `content` of type `content_type`.
        This module also defines functions to recognise the C and java
        string types.

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Type for string expressions used by the string solver. These string
///   expressions contain a field `length`, of type `index_type`, a field
///   `content` of type `content_type`. This module also defines functions to
///   recognise the C and java string types.

#ifndef CPROVER_UTIL_REFINED_STRING_TYPE_H
#define CPROVER_UTIL_REFINED_STRING_TYPE_H

#include "cprover_prefix.h"
#include "std_types.h"

// Internal type used for string refinement
class refined_string_typet: public struct_typet
{
public:
  refined_string_typet(const typet &index_type, const typet &char_type);

  // Type for the content (list of characters) of a string
  const array_typet &get_content_type() const
  {
    PRECONDITION(components().size()==2);
    return to_array_type(components()[1].type());
  }

  const typet &get_char_type() const
  {
    return get_content_type().subtype();
  }

  const typet &get_index_type() const
  {
    PRECONDITION(components().size()==2);
    return components()[0].type();
  }
};

inline bool is_refined_string_type(const typet &type)
{
    return
      type.id()==ID_struct &&
      to_struct_type(type).get_tag()==CPROVER_PREFIX"refined_string_type";
}

extern inline const refined_string_typet &to_refined_string_type(
  const typet &type)
{
  PRECONDITION(is_refined_string_type(type));
  return static_cast<const refined_string_typet &>(type);
}

#endif
