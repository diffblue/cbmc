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

#include "refined_string_type.h"

#include <util/cprover_prefix.h>

refined_string_typet::refined_string_typet(
  const typet &index_type, const typet &char_type)
{
  infinity_exprt infinite_index(index_type);
  array_typet char_array(char_type, infinite_index);
  components().emplace_back("length", index_type);
  components().emplace_back("content", char_array);
  set_tag(CPROVER_PREFIX"refined_string_type");
}

/// \par parameters: a type
/// \return Boolean telling whether the input is a refined string type
bool refined_string_typet::is_refined_string_type(const typet &type)
{
  return
    type.id()==ID_struct &&
    to_struct_type(type).get_tag()==CPROVER_PREFIX"refined_string_type";
}

